/*
 *  LLVM AntiClassDump Pass
 *  Zhang@University of Glasgow
 *
 */

#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Obfuscation/AntiClassDump.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <cstdlib>
#include <iostream>
#include <regex>
#include <string>
#include <cstring>
#include <algorithm>
using namespace llvm;
using namespace std;
using namespace Obfuscation;
namespace llvm {
struct AntiClassDump : public ModulePass {
        static char ID;
        AntiClassDump() : ModulePass(ID) {
        }
        bool runOnModule(Module &M) override {
                map<string /*sub*/,string /*sup*/> localdep;//For sorting out class dependencies
                map<string /*sub*/,string /*sup*/> externdep;
                deque<string> localClsList;
                Function* ctor=Function::Create(FunctionType::get(Type::getVoidTy(M.getContext()),ArrayRef<Type*>(),false),GlobalValue::LinkageTypes::PrivateLinkage,M.getName()+"newLoad",&M);
                BasicBlock* EntryBB=BasicBlock::Create(M.getContext(),"",ctor);
                for (auto GVI = M.global_begin(); GVI != M.global_end();
                     GVI++) { // Iterate GVs for ClassList
                        GlobalVariable &GV = *GVI;
                        if (GV.hasInitializer() &&GV.getName().str().find("OBJC_CLASS_$_") != string::npos) {
                                ConstantStruct* CS=static_cast<ConstantStruct*>(GV.getInitializer());
                                GlobalVariable* SuperClassGV=static_cast<GlobalVariable*>(CS->getAggregateElement(1));
                                string clsName=GV.getName().str();
                                clsName.replace(clsName.find("OBJC_CLASS_$_"),strlen("OBJC_CLASS_$_"),"");
                                if(SuperClassGV!=nullptr) {
                                        string supName=SuperClassGV->getName().str();
                                        supName.replace(supName.find("OBJC_CLASS_$_"),strlen("OBJC_CLASS_$_"),"");
                                        if(SuperClassGV->hasInitializer()) {//Local Dep
                                                localdep[clsName]=supName;
                                                localClsList.push_back(clsName);
                                        }
                                        else{
                                                externdep[clsName]=supName;
                                        }
                                }
                                else{
                                        //New root class.Need to pass NULL to objc_allocateClassPair
                                        //For simplicity, we use invalid base class name
                                        externdep[clsName]="1 2 3 4 5 6 7 8 9 0";
                                }
                        }
                }
                vector<string> allocatedClasses;//For status preservation.
                //We alloca external dependencies first
                for(std::map<string,string>::iterator iter = externdep.begin(); iter != externdep.end(); ++iter)
                {
                        string subCls=iter->first;
                        string supCls=iter->second;
                        errs()<<"Handling BasicClass:"<<subCls<<" Base:"<<supCls<<"\n";
                        HandleClass(subCls,supCls,EntryBB);
                        allocatedClasses.push_back(subCls);
                }
                //Handle Local Dep By pushing Non-Existing Base to the back of the queue,create otherwise
                while(localClsList.size()!=0) {
                        string cls=localClsList.front();
                        localClsList.pop_front();
                        if(localdep.find(cls)==localdep.end()) {
                                localClsList.push_back(cls);
                        }
                        else{
                                errs()<<"Handling Class:"<<cls<<" Base:"<<localdep[cls]<<"\n";
                                HandleClass(cls,localdep[cls],EntryBB);
                        }
                }
                return false;
        } // runOnModule
        void HandleClass(string subName,string supCls,BasicBlock* BB){
                Module *M=BB->getModule();
                //ObjC Runtime Declarations
                FunctionType* IMPType=FunctionType::get(Type::getInt8PtrTy(M->getContext()),{Type::getInt8PtrTy(M->getContext()),Type::getInt8PtrTy(M->getContext())},true);
                PointerType* IMPPointerType=PointerType::get(IMPType,0);
                vector<Type *> classReplaceMethodTypeArgs;
                classReplaceMethodTypeArgs.push_back(Type::getInt8PtrTy(M->getContext()));
                classReplaceMethodTypeArgs.push_back(Type::getInt8PtrTy(M->getContext()));
                classReplaceMethodTypeArgs.push_back(IMPPointerType);
                classReplaceMethodTypeArgs.push_back(Type::getInt8PtrTy(M->getContext()));
                FunctionType *class_replaceMethod_type =
                     FunctionType::get(IMPPointerType, classReplaceMethodTypeArgs,false);
                Function *class_replaceMethod = cast<Function>(M->getOrInsertFunction("class_replaceMethod", class_replaceMethod_type));
                FunctionType *sel_registerName_type =
                     FunctionType::get(Type::getInt8PtrTy(M->getContext()),
                                       {Type::getInt8PtrTy(M-> getContext())}, false);
                Function *sel_registerName = dyn_cast<Function>(
                     M->getOrInsertFunction("sel_registerName", sel_registerName_type));
                vector<Type*> allocaClsTypeVector;
                allocaClsTypeVector.push_back(Type::getInt8PtrTy(M->getContext()));
                allocaClsTypeVector.push_back(Type::getInt8PtrTy(M->getContext()));
                allocaClsTypeVector.push_back(Type::getInt64Ty(M->getContext()));
                FunctionType *allocaClsType =FunctionType::get(Type::getInt8PtrTy(M->getContext()),
                                                               ArrayRef<Type*>(allocaClsTypeVector), false);
                Function *objc_allocateClassPair = cast<Function>(
                        M->getOrInsertFunction("objc_allocateClassPair",allocaClsType));
                FunctionType *objc_getClass_type =
                        FunctionType::get(Type::getInt8PtrTy(M->getContext()),
                                          {Type::getInt8PtrTy(M->getContext())}, false);
                Function *objc_getClass = dyn_cast<Function>(
                        M->getOrInsertFunction("objc_getClass", objc_getClass_type));
                Function *objc_getMetaClass = dyn_cast<Function>(
                             M->getOrInsertFunction("objc_getMetaClass", objc_getClass_type));
                //End ObjC Runtime Declarations

                errs()<<"Creating Class:"<<subName<<"\n";
                IRBuilder<> IRB(BB);
                Value* BaseClsName=IRB.CreateGlobalStringPtr(StringRef(supCls));
                Value* ClsName=IRB.CreateGlobalStringPtr(StringRef(subName));
                CallInst* BaseClass=IRB.CreateCall(objc_getClass,{BaseClsName});
                CallInst* Cls=IRB.CreateCall(objc_allocateClassPair,{BaseClass,ClsName,ConstantInt::get(Type::getInt64Ty(M->getContext()),0)});
                CallInst* MetaCls=IRB.CreateCall(objc_getMetaClass,{ClsName});

                //Now add methods and ivar
                errs()<<"Adding Methods For Class:"<<subName<<"\n";
                string ClassMethodListGVName = "\01l_OBJC_$_CLASS_METHODS_";
                ClassMethodListGVName.append(subName);
                string InstanceMethodListGVName = "\01l_OBJC_$_INSTANCE_METHODS_";
                InstanceMethodListGVName.append(subName);
                GlobalVariable *ClassMethodListGV =
                        M->getGlobalVariable(ClassMethodListGVName, true);
                GlobalVariable *InstanceMethodListGV =
                        M->getGlobalVariable(StringRef(InstanceMethodListGVName), true);
                // Collect Methods.
                // Construct +initialize if needed
                vector<tuple<string /*SEL*/, string /*Method Signature*/,Function * /*IMP*/> > ClassMethodList;
                vector<tuple<string /*SEL*/, string /*Method Signature*/,Function * /*IMP*/> > InstanceMethodList;
                if (ClassMethodListGV!=nullptr&&ClassMethodListGV->hasInitializer()) {
                        ConstantStruct *Init = reinterpret_cast<ConstantStruct *>(
                                ClassMethodListGV->getInitializer());
                        ConstantArray *objc_method_struct =
                                dyn_cast<ConstantArray>(Init->getOperand(2));
                        for (unsigned int idx = 0; idx < objc_method_struct->getNumOperands();
                             idx++) {
                                ConstantExpr *CEMethodName = dyn_cast<ConstantExpr>(
                                        dyn_cast<Constant>(objc_method_struct->getOperand(idx))
                                        ->getOperand(0));
                                ConstantExpr *CEMethodSignature = dyn_cast<ConstantExpr>(
                                        dyn_cast<Constant>(objc_method_struct->getOperand(idx))
                                        ->getOperand(1));
                                ConstantExpr *CEBCIFunctionPointer = dyn_cast<ConstantExpr>(
                                        dyn_cast<Constant>(objc_method_struct->getOperand(idx))
                                        ->getOperand(2));
                                GlobalVariable *GVMethodName =
                                        dyn_cast<GlobalVariable>(CEMethodName->getOperand(0));
                                GlobalVariable *GVMethodSig =
                                        dyn_cast<GlobalVariable>(CEMethodSignature->getOperand(0));
                                StringRef MethodName =
                                        dyn_cast<ConstantDataArray>(GVMethodName->getInitializer())
                                        ->getAsString();
                                StringRef MethodSig =
                                        dyn_cast<ConstantDataArray>(GVMethodSig->getInitializer())
                                        ->getAsString();
                                Function *IMP =
                                        dyn_cast<Function>(CEBCIFunctionPointer->getOperand(0));
                                ClassMethodList.push_back(
                                        make_tuple(MethodName.str(), MethodSig.str(), IMP));

                        }
                }
                if (InstanceMethodListGV!=nullptr&&InstanceMethodListGV->hasInitializer()) {
                        ConstantStruct *Init = reinterpret_cast<ConstantStruct *>(
                                InstanceMethodListGV->getInitializer());
                        ConstantArray *objc_method_struct =
                                dyn_cast<ConstantArray>(Init->getOperand(2));
                        for (unsigned int idx = 0; idx < objc_method_struct->getNumOperands();
                             idx++) {
                                ConstantExpr *CEMethodName = dyn_cast<ConstantExpr>(
                                        dyn_cast<Constant>(objc_method_struct->getOperand(idx))
                                        ->getOperand(0));
                                ConstantExpr *CEMethodSignature = dyn_cast<ConstantExpr>(
                                        dyn_cast<Constant>(objc_method_struct->getOperand(idx))
                                        ->getOperand(1));
                                ConstantExpr *CEBCIFunctionPointer = dyn_cast<ConstantExpr>(
                                        dyn_cast<Constant>(objc_method_struct->getOperand(idx))
                                        ->getOperand(2));
                                GlobalVariable *GVMethodName =
                                        dyn_cast<GlobalVariable>(CEMethodName->getOperand(0));
                                GlobalVariable *GVMethodSig =
                                        dyn_cast<GlobalVariable>(CEMethodSignature->getOperand(0));
                                StringRef MethodName =
                                        dyn_cast<ConstantDataArray>(GVMethodName->getInitializer())
                                        ->getAsString();
                                StringRef MethodSig =
                                        dyn_cast<ConstantDataArray>(GVMethodSig->getInitializer())
                                        ->getAsString();
                                Function *IMP =
                                        dyn_cast<Function>(CEBCIFunctionPointer->getOperand(0));
                                InstanceMethodList.push_back(
                                        make_tuple(MethodName.str(), MethodSig.str(), IMP));
                        }

                }
                //Now perform addMethod calls
                for(tuple<string, string, Function *> IMtuple:InstanceMethodList) {
                        errs() << "Instance MethodSig:" << get<1>(IMtuple) << "\n"
                               << "MethodName:" << get<0>(IMtuple) << "\n"
                               << "Original Implementation Name" << get<2>(IMtuple)->getName() << "\n";
                        Value* SELStr=IRB.CreateGlobalStringPtr(StringRef(get<0>(IMtuple)));
                        Value* SEL=IRB.CreateCall(sel_registerName,{SELStr});
                        Value* SIG=IRB.CreateGlobalStringPtr(StringRef(get<1>(IMtuple)));
                        Value* IMPFunc=IRB.CreateBitCast(get<2>(IMtuple),IMPPointerType);
                        class_replaceMethod->print(errs());
                        errs()<<"\n";
                        Cls->print(errs());
                        errs()<<"\n";
                        SEL->print(errs());
                        errs()<<"\n";
                        IMPFunc->print(errs());
                        errs()<<"\n";
                        SIG->print(errs());
                        errs()<<"\n";
                        IRB.CreateCall(class_replaceMethod,{Cls,SEL,IMPFunc,SIG});
                }
                for(tuple<string, string, Function *> IMtuple:ClassMethodList) {
                        errs() << "Class MethodSig:" << get<1>(IMtuple) << "\n"
                               << "MethodName:" << get<0>(IMtuple) << "\n"
                               << "Original Implementation Name" << get<2>(IMtuple)->getName() << "\n";
                        Value* SELStr=IRB.CreateGlobalStringPtr(StringRef(get<0>(IMtuple)));
                        Value* SIG=IRB.CreateGlobalStringPtr(StringRef(get<1>(IMtuple)));
                        Value* SEL=IRB.CreateCall(sel_registerName,{SELStr});
                        Value* IMPFunc=IRB.CreateBitCast(get<2>(IMtuple),IMPPointerType);
                        IRB.CreateCall(class_replaceMethod,{MetaCls,SEL,IMPFunc,SIG});
                }
                //Now Handle Property and ivar
                //\01l_OBJC_$_PROP_LIST_
                //\01l_OBJC_$_INSTANCE_VARIABLES_
        }
        StringRef getPassName() const override{
          return "AntiClassDump";
        }

};  // struct
Pass *createAntiClassDump() {
        return new AntiClassDump();
}
} // namespace llvm

char AntiClassDump::ID = 0;
/*
   //ObjC runtime definitions

   //*/
