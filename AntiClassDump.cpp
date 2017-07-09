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
#include "llvm/Transforms/Obfuscation/Obfuscation.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <cstdlib>
#include <iostream>
#include <regex>
#include <string>
#include <cstring>
using namespace llvm;
using namespace std;
static string obfcharacters = "qwertyuiopasdfghjklzxcvbnm1234567890";
/*static const char *OCNAMEPLACEHOLDERS[] = {
        "OBJC_CLASS_$_", "OBJC_METACLASS_$_", "\01l_OBJC_CLASS_RO_$_",
        "\01l_OBJC_$_CLASS_METHODS_", "\01l_OBJC_METACLASS_RO_$_"
};*/
namespace llvm {
struct AntiClassDump : public ModulePass {
        static char ID;
        AntiClassDump() : ModulePass(ID) {
        }
        string randomString(int length) {
                string name;
                name.resize(length);
                for (int i = 0; i < length; i++) {
                        name[i] = obfcharacters[rand() % (obfcharacters.length())];
                }
                return name;
        }
        bool runOnModule(Module &M) override {

                // TODO: Dynamic Create Classes
                errs() << "It's not a pleasant thought John.\nBut I have this terrible "
                        "feeling from time to time that we might all just be humans.\n";
                FunctionType *sel_registerName_type =
                        FunctionType::get(Type::getInt8PtrTy(M.getContext()),
                                          {Type::getInt8PtrTy(M.getContext())}, false);
                Function *sel_registerName = dyn_cast<Function>(
                        M.getOrInsertFunction("sel_registerName", sel_registerName_type));
                FunctionType *objc_getClass_type =
                        FunctionType::get(M.getTypeByName("struct._class_t")->getPointerTo(),
                                          {Type::getInt8PtrTy(M.getContext())}, false);
                Function *objc_getClass = dyn_cast<Function>(
                        M.getOrInsertFunction("objc_getClass", objc_getClass_type));
                Function *objc_getMetaClass = dyn_cast<Function>(
                        M.getOrInsertFunction("objc_getMetaClass", objc_getClass_type));
                vector<Type *> Args;
                Args.push_back(M.getTypeByName("struct._class_t")->getPointerTo());
                Args.push_back(Type::getInt8PtrTy(M.getContext()));
                Args.push_back(Type::getInt8PtrTy(M.getContext()));
                Args.push_back(Type::getInt8PtrTy(M.getContext()));
                FunctionType *class_replaceMethod_type =
                        FunctionType::get(Type::getInt8PtrTy(M.getContext()), Args, false);
                Function *class_replaceMethod = cast<Function>(
                        M.getOrInsertFunction("class_replaceMethod", class_replaceMethod_type));
                vector<string> ClassNameList;
                for (auto GVI = M.global_begin(); GVI != M.global_end();
                     GVI++) { // Iterate GVs for ClassList
                        GlobalVariable &GV = *GVI;
                        if (GV.getName().str().find("OBJC_CLASS_NAME_") != string::npos) {
                                ConstantDataSequential* CDA=dyn_cast<ConstantDataSequential>(GV.getInitializer());
                                if(CDA!=nullptr){
                                  if(CDA->isCString()){
                                    ClassNameList.push_back(CDA->getAsCString ());
                                  }
                                  else if(CDA->isString ()){
                                    ClassNameList.push_back(CDA->getAsString ());
                                  }
                                }
                        }

                }
                for (string className : ClassNameList) { // Actual Work
                        Function *LoadFunction = nullptr;//Pointer to +initialize
                        string ClassMethodListGVName = "\01l_OBJC_$_CLASS_METHODS_";
                        ClassMethodListGVName.append(className);
                        string InstanceMethodListGVName = "\01l_OBJC_$_INSTANCE_METHODS_";
                        InstanceMethodListGVName.append(className);
                        GlobalVariable *ClassMethodListGV =
                                M.getGlobalVariable(ClassMethodListGVName, true);
                        GlobalVariable *InstanceMethodListGV =
                                M.getGlobalVariable(StringRef(InstanceMethodListGVName), true);
                        BasicBlock* LoadBB=nullptr;//Insert BasicBlock for +initialize
                        uint64_t Flags=1337;
                        // Collect Methods.
                        // Construct +initialize if needed
                        vector<tuple<string /*SEL*/, string /*Method Signature*/,Function * /*IMP*/> > ClassMethodList;
                        vector<tuple<string /*SEL*/, string /*Method Signature*/,Function * /*IMP*/> > InstanceMethodList;
                        if (ClassMethodListGV!=nullptr&&ClassMethodListGV->hasInitializer()) {
                                ConstantStruct *Init = reinterpret_cast<ConstantStruct *>(
                                        ClassMethodListGV->getInitializer());
                                ConstantInt *FlagsCI = dyn_cast<ConstantInt>(Init->getOperand(0));
                                ConstantInt *MethodCountCI = dyn_cast<ConstantInt>(Init->getOperand(1));
                                uint64_t MethodCount = MethodCountCI->getValue().getLimitedValue();
                                Flags = FlagsCI->getValue().getLimitedValue();
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
                                        MethodCount--;
                                        if(strcmp(MethodName.str().c_str(),"initialize")==0) {//Found +initialize
                                                errs()<<"Found "<<className<<" 's +initialize:"<<MethodName.str()<<"\n";
                                                MethodCount++;//Cancel previous --
                                                LoadFunction=IMP;
                                        }
                                        else{
                                          ClassMethodList.push_back(
                                                  make_tuple(MethodName.str(), MethodSig.str(), IMP));
                                        }

                                }
                        }
                        if (InstanceMethodListGV!=nullptr&&InstanceMethodListGV->hasInitializer()) {
                                ConstantStruct *Init = reinterpret_cast<ConstantStruct *>(
                                        InstanceMethodListGV->getInitializer());
                                ConstantInt *FlagsCI = dyn_cast<ConstantInt>(Init->getOperand(0));
                                ConstantInt *MethodCountCI = dyn_cast<ConstantInt>(Init->getOperand(1));
                                uint64_t MethodCount = MethodCountCI->getValue().getLimitedValue();
                                uint64_t Flags = FlagsCI->getValue().getLimitedValue();
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
                                        MethodCount--;
                                        InstanceMethodList.push_back(
                                                make_tuple(MethodName.str(), MethodSig.str(), IMP));
                                }
                                // Construct new Instance Method Init
                                vector<Constant *> args;
                                args.push_back(ConstantInt::get(FlagsCI->getType(), Flags));
                                args.push_back(ConstantInt::get(MethodCountCI->getType(),0));
                                args.push_back(ConstantArray::get(ArrayType::get(M.getTypeByName("struct._objc_method"),0), {}));
                                vector<Type *> argsTypes;
                                for(size_t i=0;i<args.size ();i++){
                                  argsTypes.push_back(args[i]->getType());
                                }
                                ConstantStruct *newInit = reinterpret_cast<ConstantStruct *>(
                                        ConstantStruct::get(StructType::create(ArrayRef<Type *>(argsTypes)),ArrayRef<Constant *>(args)));
                                string GVName=ClassMethodListGVName;
                                GlobalVariable* newGV=new GlobalVariable (M,newInit->getType(),InstanceMethodListGV->isConstant(),InstanceMethodListGV->getLinkage(),newInit,"",nullptr,InstanceMethodListGV->getThreadLocalMode ());
                                while (!InstanceMethodListGV->use_empty()) {
                                    auto &U = *InstanceMethodListGV->use_begin();
                                    U.set(newGV);
                                }
                                InstanceMethodListGV->eraseFromParent();
                                newGV->setName(Twine(GVName));

                        }
                        //Create New +initialize
                        if(LoadFunction==nullptr) {//Existing +initialize not found.Create new one
                                errs()<<"Creating new +initialize for:"<<className<<"\n";
                                vector<Type*> argTypes;
                                argTypes.push_back(Type::getInt8PtrTy(M.getContext()));//id
                                argTypes.push_back(Type::getInt8PtrTy(M.getContext()));//SEL
                                LoadFunction=Function::Create(FunctionType::get(Type::getVoidTy(M.getContext()),ArrayRef<Type*>(argTypes),false),GlobalValue::LinkageTypes::ExternalLinkage,className+"newLoad",&M);
                        }
                        //Create +initialize struct
                        vector<Constant*> GEPIndexArrayRef;
                        GEPIndexArrayRef.push_back(ConstantInt::get(Type::getInt32Ty(M.getContext()),0));
                        GEPIndexArrayRef.push_back(ConstantInt::get(Type::getInt32Ty(M.getContext()),0));
                        vector<Constant*> MS;
                        ConstantDataArray* SELRef=dyn_cast<ConstantDataArray>(ConstantDataArray::getString(M.getContext(),"initialize"));
                        ConstantDataArray* SigRef=dyn_cast<ConstantDataArray>(ConstantDataArray::getString(M.getContext(),"v16@0:8"));
                        Constant* IMPBCI=ConstantExpr::getPointerCast(LoadFunction,Type::getInt8PtrTy(M.getContext()));
                        GlobalVariable* SELGV=new GlobalVariable(M, SELRef->getType(),true, GlobalValue::InternalLinkage,SELRef);
                        GlobalVariable* SIGGV=new GlobalVariable(M, SigRef->getType(),true, GlobalValue::InternalLinkage,SigRef);
                        SELGV->setSection("__TEXT,__objc_methname,cstring_literals");
                        SIGGV->setSection("__TEXT,__objc_methtype,cstring_literals");
                        SELGV->setName("");
                        SIGGV->setName("");
                        Constant* SELRefGEP=ConstantExpr::getGetElementPtr(SELGV->getValueType(),SELGV,ArrayRef<Constant*>(GEPIndexArrayRef),true);
                        Constant* SIGRefGEP=ConstantExpr::getGetElementPtr(SIGGV->getValueType(),SIGGV,ArrayRef<Constant*>(GEPIndexArrayRef),true);
                        MS.push_back(SELRefGEP);
                        MS.push_back(SIGRefGEP);
                        MS.push_back(IMPBCI);
                        Constant *OCMethodStruct=ConstantStruct::get(dyn_cast<StructType>(M.getTypeByName("struct._objc_method")),ArrayRef<Constant*>(MS));
                        vector<Constant *> args;
                        args.push_back(ConstantInt::get(Type::getInt32Ty(M.getContext()),Flags==1337?24:Flags));
                        args.push_back(ConstantInt::get(Type::getInt32Ty(M.getContext()), 1));
                        args.push_back(ConstantArray::get(ArrayType::get(M.getTypeByName("struct._objc_method"),1),{OCMethodStruct}));
                        vector<Type *> argsTypes;
                        for(size_t i=0;i<args.size ();i++){
                          argsTypes.push_back(args[i]->getType());
                        }
                        ConstantStruct *newInit = dyn_cast<ConstantStruct>(
                                ConstantStruct::get(StructType::create(ArrayRef<Type *>(argsTypes)),ArrayRef<Constant *>(args)));
                        string GVName=ClassMethodListGVName;
                        GlobalVariable* newGV=new GlobalVariable (M,newInit->getType(),true,GlobalValue::LinkageTypes::InternalLinkage,newInit);
                        if(ClassMethodListGV!=nullptr){
                          while (!ClassMethodListGV->use_empty()) {
                            auto &U = *ClassMethodListGV->use_begin();
                            U.set(newGV);
                          }
                          ClassMethodListGV->eraseFromParent();
                        }
                        newGV->setName(Twine(GVName));
                        //Insert +initialize IR
                        Instruction* Term=nullptr;
                        if(LoadFunction->empty()){
                          LoadBB=BasicBlock::Create(M.getContext(),"",LoadFunction);
                          IRBuilder<> IRB(LoadBB);
                          Term=IRB.CreateRetVoid ();
                        }
                        else{
                          LoadBB=&(LoadFunction->getEntryBlock ());
                          Term=LoadBB->getTerminator ();

                        }
                        IRBuilder<> IRB(Term);
                        Value* AnotherClassName=IRB.CreateGlobalStringPtr(StringRef(className));
                        for(tuple<string, string, Function *> IMtuple:InstanceMethodList) {
                                errs() << "Instance MethodSig:" << get<1>(IMtuple) << "\n"
                                       << "MethodName:" << get<0>(IMtuple) << "\n"
                                       << "Original Implementation Name" << get<2>(IMtuple)->getName() << "\n";
                                Value* SELStr=IRB.CreateGlobalStringPtr(StringRef(get<0>(IMtuple)));
                                Value* SEL=IRB.CreateCall(sel_registerName,{SELStr});
                                Value* SIG=IRB.CreateGlobalStringPtr(StringRef(get<1>(IMtuple)));
                                Value* IMPFunc=IRB.CreateBitCast(get<2>(IMtuple),Type::getInt8PtrTy(M.getContext()));
                                CallInst* Cls=IRB.CreateCall(objc_getClass,{AnotherClassName});
                                IRB.CreateCall(class_replaceMethod,{Cls,SEL,IMPFunc,SIG});
                        }
                        for(tuple<string, string, Function *> IMtuple:ClassMethodList) {
                                errs() << "Class MethodSig:" << get<1>(IMtuple) << "\n"
                                       << "MethodName:" << get<0>(IMtuple) << "\n"
                                       << "Original Implementation Name" << get<2>(IMtuple)->getName() << "\n";
                                Value* SELStr=IRB.CreateGlobalStringPtr(StringRef(get<0>(IMtuple)));
                                Value* SIG=IRB.CreateGlobalStringPtr(StringRef(get<1>(IMtuple)));
                                Value* SEL=IRB.CreateCall(sel_registerName,{SELStr});
                                Value* IMPFunc=IRB.CreateBitCast(get<2>(IMtuple),Type::getInt8PtrTy(M.getContext()));
                                CallInst* Cls=IRB.CreateCall(objc_getMetaClass,{AnotherClassName});
                                IRB.CreateCall(class_replaceMethod,{Cls,SEL,IMPFunc,SIG});
                        }
                        //Inject IR into +initialize

                }

                return false;
        } // runOnModule
};  // struct
Pass *createAntiClassDump() {
        return new AntiClassDump();
}
} // namespace llvm

char AntiClassDump::ID = 0;
