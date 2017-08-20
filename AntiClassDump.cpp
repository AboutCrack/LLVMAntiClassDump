/*
 *  LLVM AntiClassDump Pass
 *  Zhang@University of Glasgow
 *
 */

#include "llvm/Transforms/Obfuscation/AntiClassDump.h"
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
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <algorithm>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <regex>
#include <string>
#include <tgmath.h>
using namespace llvm;
using namespace std;
using namespace Obfuscation;
namespace llvm {
struct AntiClassDump : public ModulePass {
  static char ID;
  AntiClassDump() : ModulePass(ID) {}
  bool runOnModule(Module &M) override {
    map<string /*sub*/, string /*sup*/>
        localdep; // For sorting out class dependencies
    map<string /*sub*/, string /*sup*/> externdep;
    deque<string> localClsList;
    Function *ctor = Function::Create(
        FunctionType::get(Type::getVoidTy(M.getContext()), ArrayRef<Type *>(),
                          false),
        GlobalValue::LinkageTypes::PrivateLinkage, M.getName() + "newLoad", &M);
    BasicBlock *EntryBB = BasicBlock::Create(M.getContext(), "", ctor);
    for (auto GVI = M.global_begin(); GVI != M.global_end();
         GVI++) { // Iterate GVs for ClassList
      GlobalVariable &GV = *GVI;
      if (GV.hasInitializer() &&
          GV.getName().str().find("OBJC_CLASS_$_") != string::npos) {
        ConstantStruct *CS = static_cast<ConstantStruct *>(GV.getInitializer());
        GlobalVariable *SuperClassGV =
            static_cast<GlobalVariable *>(CS->getAggregateElement(1));
        string clsName = GV.getName().str();
        clsName.replace(clsName.find("OBJC_CLASS_$_"), strlen("OBJC_CLASS_$_"),
                        "");
        if (SuperClassGV != nullptr) {
          string supName = SuperClassGV->getName().str();
          supName.replace(supName.find("OBJC_CLASS_$_"),
                          strlen("OBJC_CLASS_$_"), "");
          if (SuperClassGV->hasInitializer()) { // Local Dep
            localdep[clsName] = supName;
            localClsList.push_back(clsName);
          } else {
            externdep[clsName] = supName;
          }
        } else {
          // New root class.Need to pass NULL to objc_allocateClassPair
          // For simplicity, we use invalid base class name
          externdep[clsName] = "1 2 3 4 5 6 7 8 9 0";
        }
      }
    }
    vector<string> allocatedClasses; // For status preservation.
    // We alloca external dependencies first
    for (std::map<string, string>::iterator iter = externdep.begin();
         iter != externdep.end(); ++iter) {
      string subCls = iter->first;
      string supCls = iter->second;
      errs() << "Handling BasicClass:" << subCls << " Base:" << supCls << "\n";
      HandleClass(subCls, supCls, EntryBB);
      allocatedClasses.push_back(subCls);
    }
    // Handle Local Dep By pushing Non-Existing Base to the back of the
    // queue,create otherwise
    while (localClsList.size() != 0) {
      string cls = localClsList.front();
      localClsList.pop_front();
      if (localdep.find(cls) == localdep.end()) {
        localClsList.push_back(cls);
      } else {
        errs() << "Handling Class:" << cls << " Base:" << localdep[cls] << "\n";
        HandleClass(cls, localdep[cls], EntryBB);
      }
    }
#warning Dumb Class Dependency Resolve Algorithm, Only Stable at LTO Stage unless we leave class struct intact
    // TODO: Handle Protocols

    IRBuilder<> IRB(EntryBB);
    IRB.CreateRetVoid();
    // Insert our ctor into llvm.global_ctor
    FunctionType* ctorFuncType=FunctionType::get(Type::getVoidTy(M.getContext()), ArrayRef<Type*>(), false);
    StructType* ctorType=StructType::create("ctor_type",Type::getInt32Ty(M.getContext()),ctorFuncType->getPointerTo(),Type::getInt8PtrTy(M.getContext()));
    GlobalVariable* oldctorGV=M.getNamedGlobal("llvm.global_ctors");
    vector<Constant*> oldCtors;
    if(oldctorGV!=nullptr&&oldctorGV->hasDefinitiveInitializer()){//Save old ctors if exists
        ConstantArray* CA=reinterpret_cast<ConstantArray*>(oldctorGV->getInitializer());
        for(uint64_t i=0;i<CA->getType()->getNumElements();i++){
            oldCtors.push_back(CA->getAggregateElement(i));
        }
        oldctorGV->eraseFromParent();
        
    }
    //Reconstruct new llvm.global_ctors
      vector<Constant*> newCtorArgs;
    newCtorArgs.push_back(ConstantInt::get(Type::getInt32Ty(M.getContext()), 1));
    newCtorArgs.push_back(ctor);
      newCtorArgs.push_back(Constant::getNullValue(Type::getInt8PtrTy(M.getContext())));
    Constant* newCtor=ConstantStruct::get(ctorType, ArrayRef<Constant*>(newCtorArgs));
    oldCtors.push_back(newCtor);
    ArrayType* newCtorGVInitAT=ArrayType::get(ctorType, oldCtors.size());
    Constant* newCtorGVInit=ConstantArray::get(newCtorGVInitAT, ArrayRef<Constant*>(oldCtors));
    GlobalVariable* newctorGV=new GlobalVariable(M,newCtorGVInitAT,false,GlobalValue::LinkageTypes::AppendingLinkage,newCtorGVInit,Twine("llvm.global_ctors"));
      errs()<<"Created New Global Ctor:";
    newctorGV->dump();
    // TODO: Clean up old structs
      for(auto GVI = M.global_begin(); GVI != M.global_end();
          GVI++){
          GlobalVariable &GV = *GVI;
          if(GV.hasDefinitiveInitializer()){
              if(GV.getName().startswith("OBJC_CLASS_$_")){
                  StringRef clsName(GV.getName().str());
                  clsName=clsName.ltrim(clsName.find("OBJC_CLASS_$_"));
                  for(auto U=GV.user_begin();U!=GV.user_end();U++){
                      if(Instruction* I=dyn_cast<Instruction>(*U)){
                          IRBuilder<> IRB(I);
                          Function* objc_getClass=M.getFunction("objc_getClass");
                          Value* CName=IRB.CreateGlobalStringPtr(clsName);
                          Value* Inst=IRB.CreateCall(objc_getClass, {CName});
                          I->dump();
                          Inst->dump();
                          //I->replaceAllUsesWith(BCInst);
                         // U=Inst;
                      }
                  }
              }
          }
      }
    return false;
  } // runOnModule
    
    
  void HandleClass(string subName, string supCls, BasicBlock *BB) {
    Module *M = BB->getModule();
    Type* Int64Ty=Type::getInt64Ty(M->getContext());
    Type* Int32Ty=Type::getInt32Ty(M->getContext());
    Type* Int8PtrTy=Type::getInt8PtrTy(M->getContext());
    // ObjC Runtime Declarations
    FunctionType *IMPType =
        FunctionType::get(Int8PtrTy,
                          {Int8PtrTy,
                           Int8PtrTy},
                          true);
    PointerType *IMPPointerType = PointerType::get(IMPType, 0);
    vector<Type *> classReplaceMethodTypeArgs;
    classReplaceMethodTypeArgs.push_back(Int8PtrTy);
    classReplaceMethodTypeArgs.push_back(Int8PtrTy);
    classReplaceMethodTypeArgs.push_back(IMPPointerType);
    classReplaceMethodTypeArgs.push_back(Int8PtrTy);
    FunctionType *class_replaceMethod_type =
        FunctionType::get(IMPPointerType, classReplaceMethodTypeArgs, false);
    Function *class_replaceMethod = cast<Function>(M->getOrInsertFunction(
        "class_replaceMethod", class_replaceMethod_type));
    FunctionType *sel_registerName_type =
        FunctionType::get(Int8PtrTy,
                          {Int8PtrTy}, false);
    Function *sel_registerName = dyn_cast<Function>(
        M->getOrInsertFunction("sel_registerName", sel_registerName_type));
    vector<Type *> allocaClsTypeVector;
    allocaClsTypeVector.push_back(Int8PtrTy);
    allocaClsTypeVector.push_back(Int8PtrTy);
    allocaClsTypeVector.push_back(Int64Ty);
    FunctionType *allocaClsType =
        FunctionType::get(Int8PtrTy,
                          ArrayRef<Type *>(allocaClsTypeVector), false);
    Function *objc_allocateClassPair = cast<Function>(
        M->getOrInsertFunction("objc_allocateClassPair", allocaClsType));
    FunctionType *objc_getClass_type =
        FunctionType::get(Int8PtrTy,
                          {Int8PtrTy}, false);
    Function *objc_getClass = dyn_cast<Function>(
        M->getOrInsertFunction("objc_getClass", objc_getClass_type));
    Function *objc_getMetaClass = dyn_cast<Function>(
        M->getOrInsertFunction("objc_getMetaClass", objc_getClass_type));
    FunctionType *objc_registerClassPair_type =
        FunctionType::get(Type::getVoidTy(M->getContext()),
                          {Int8PtrTy}, false);
    Function *objc_registerClassPair =
        dyn_cast<Function>(M->getOrInsertFunction("objc_registerClassPair",
                                                  objc_registerClassPair_type));

    StructType* objc_property_attribute_t_type=reinterpret_cast<StructType*>(M->getTypeByName("struct.objc_property_attribute_t"));
    AttributeSet SExtAttr=AttributeSet();
    SExtAttr=SExtAttr.addAttribute(M->getContext(),Attribute::SExt);
    AttributeSet ZExtAttr=AttributeSet();
    ZExtAttr=ZExtAttr.addAttribute(M->getContext(),Attribute::ZExt);
    vector<AttributeSet> c_aIArgAttributes;
    c_aIArgAttributes.push_back(AttributeSet());
    c_aIArgAttributes.push_back(AttributeSet());
    c_aIArgAttributes.push_back(AttributeSet());
    c_aIArgAttributes.push_back(ZExtAttr);
    c_aIArgAttributes.push_back(AttributeSet());
    AttributeList  class_addIvar_attr=AttributeList::get(M->getContext(),AttributeSet(),SExtAttr,ArrayRef<AttributeSet>(c_aIArgAttributes));
    Constant* class_addIvar_const=M->getOrInsertFunction("class_addIvar",class_addIvar_attr,Type::getInt8Ty(M->getContext()),Int8PtrTy,Int8PtrTy,Int64Ty,Type::getInt8Ty (M->getContext()),Int8PtrTy);
    //The Int64Ty above should be Int32Ty on 32bit device
    //Need runtime check based on Datalayout
    AttributeList class_addProperty_attr=AttributeList::get(M->getContext(),AttributeSet(),SExtAttr,ArrayRef<AttributeSet>());
    Constant* class_addProperty_const=M->getOrInsertFunction("class_addProperty",class_addProperty_attr,Type::getInt8Ty(M->getContext()),Int8PtrTy,Int8PtrTy,objc_property_attribute_t_type->getPointerTo(),Int32Ty);
    Function* class_addIvar=dyn_cast<Function>(class_addIvar_const);
    Function* class_addProperty=dyn_cast<Function>(class_addProperty_const);
    //End ObjC Runtime Function Declaration
    errs() << "Creating Class:" << subName << "\n";
    IRBuilder<> IRB(BB);
    Value *BaseClsName = IRB.CreateGlobalStringPtr(StringRef(supCls));
    Value *ClsName = IRB.CreateGlobalStringPtr(StringRef(subName));
    CallInst *BaseClass = IRB.CreateCall(objc_getClass, {BaseClsName});
    CallInst *Cls = IRB.CreateCall(
        objc_allocateClassPair,
        {BaseClass, ClsName,
         ConstantInt::get(Int64Ty, 0)});
    CallInst *MetaCls = IRB.CreateCall(objc_getMetaClass, {ClsName});

    // Now add methods and ivar
    errs() << "Adding Methods For Class:" << subName << "\n";
    string ClassMethodListGVName = "\01l_OBJC_$_CLASS_METHODS_";
    ClassMethodListGVName.append(subName);
    string InstanceMethodListGVName = "\01l_OBJC_$_INSTANCE_METHODS_";
    InstanceMethodListGVName.append(subName);
    GlobalVariable *ClassMethodListGV =
        M->getGlobalVariable(ClassMethodListGVName, true);
    GlobalVariable *InstanceMethodListGV =
        M->getGlobalVariable(StringRef(InstanceMethodListGVName), true);
    vector<
        tuple<string /*SEL*/, string /*Method Signature*/, Function * /*IMP*/>>
        ClassMethodList;
    vector<
        tuple<string /*SEL*/, string /*Method Signature*/, Function * /*IMP*/>>
        InstanceMethodList;
    if (ClassMethodListGV != nullptr && ClassMethodListGV->hasInitializer()) {
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
        Function *IMP = dyn_cast<Function>(CEBCIFunctionPointer->getOperand(0));
        ClassMethodList.push_back(
            make_tuple(MethodName.str(), MethodSig.str(), IMP));
      }
    }
    if (InstanceMethodListGV != nullptr &&
        InstanceMethodListGV->hasInitializer()) {
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
        Function *IMP = dyn_cast<Function>(CEBCIFunctionPointer->getOperand(0));
        InstanceMethodList.push_back(
            make_tuple(MethodName.str(), MethodSig.str(), IMP));
      }
    }
    // Now perform addMethod calls
    for (tuple<string, string, Function *> IMtuple : InstanceMethodList) {
      errs() << "Instance MethodSig:" << get<1>(IMtuple) << "\n"
             << "MethodName:" << get<0>(IMtuple) << "\n"
             << "Original Implementation Name" << get<2>(IMtuple)->getName()
             << "\n";
      Value *SELStr = IRB.CreateGlobalStringPtr(StringRef(get<0>(IMtuple)));
      Value *SEL = IRB.CreateCall(sel_registerName, {SELStr});
      Value *SIG = IRB.CreateGlobalStringPtr(StringRef(get<1>(IMtuple)));
      Value *IMPFunc = IRB.CreateBitCast(get<2>(IMtuple), IMPPointerType);
      IRB.CreateCall(class_replaceMethod, {Cls, SEL, IMPFunc, SIG});
    }
    for (tuple<string, string, Function *> IMtuple : ClassMethodList) {
      errs() << "Class MethodSig:" << get<1>(IMtuple) << "\n"
             << "MethodName:" << get<0>(IMtuple) << "\n"
             << "Original Implementation Name" << get<2>(IMtuple)->getName()
             << "\n";
      Value *SELStr = IRB.CreateGlobalStringPtr(StringRef(get<0>(IMtuple)));
      Value *SIG = IRB.CreateGlobalStringPtr(StringRef(get<1>(IMtuple)));
      Value *SEL = IRB.CreateCall(sel_registerName, {SELStr});
      Value *IMPFunc = IRB.CreateBitCast(get<2>(IMtuple), IMPPointerType);
      IRB.CreateCall(class_replaceMethod, {MetaCls, SEL, IMPFunc, SIG});
    }
    // Now Handle Property and ivar
    errs() << "Adding Property and Ivars For Class:" << subName << "\n";
    string propertyListGVName = "\01l_OBJC_$_PROP_LIST_";
    propertyListGVName.append(subName);
    string ivarListGVName = "\01l_OBJC_$_INSTANCE_VARIABLES_";
    ivarListGVName.append(subName);
    GlobalVariable *propertyListGV =
        M->getGlobalVariable(propertyListGVName, true);
    GlobalVariable *ivarListGV =
        M->getGlobalVariable(StringRef(ivarListGVName), true);
    vector<tuple<GlobalVariable * /*ivarOffsetGV*/, StringRef /*IVAR NAME*/,
                 StringRef /*ivar type*/, ConstantInt * /*IVAR SIZE*/>>
        ivarList;
    vector<tuple<StringRef /*PROP NAME*/, StringRef /*PROP ATTR*/>> propList;
    if (ivarListGV != nullptr && ivarListGV->hasInitializer()) { // Collect
                                                                 // IVARs
      ConstantStruct *Init =
          reinterpret_cast<ConstantStruct *>(ivarListGV->getInitializer());
      ConstantArray *objc_ivar_struct =
          dyn_cast<ConstantArray>(Init->getOperand(2));
      for (unsigned int idx = 0; idx < objc_ivar_struct->getNumOperands();
           idx++) {
        ConstantStruct *ivarstruct =
            dyn_cast<ConstantStruct>(objc_ivar_struct->getOperand(idx));
        GlobalVariable *ivarOffsetGV =
            dyn_cast<GlobalVariable>(ivarstruct->getOperand(0));

        GlobalVariable *ivarNameGV = dyn_cast<GlobalVariable>(
            dyn_cast<ConstantExpr>(ivarstruct->getOperand(1))->getOperand(0));
        StringRef ivarName =
            dyn_cast<ConstantDataArray>(ivarNameGV->getInitializer())
                ->getAsString();
        GlobalVariable *ivarTypeGV = dyn_cast<GlobalVariable>(
            dyn_cast<ConstantExpr>(ivarstruct->getOperand(2))->getOperand(0));
        StringRef ivarType =
            dyn_cast<ConstantDataArray>(ivarTypeGV->getInitializer())
                ->getAsString();

        // index 3 on 32bit maybe? 4 on 64bit. So we just retreive the last one
        ConstantInt *ivarSize = dyn_cast<ConstantInt>(
            ivarstruct->getOperand(ivarstruct->getNumOperands() - 1));
        ivarList.push_back(
            make_tuple(ivarOffsetGV, ivarName, ivarType, ivarSize));
      }
    }
    if (propertyListGV != nullptr && propertyListGV->hasInitializer()) {
      ConstantStruct *Init =
          reinterpret_cast<ConstantStruct *>(propertyListGV->getInitializer());
      ConstantArray *objc_prop_struct =
          dyn_cast<ConstantArray>(Init->getOperand(2));
      for (unsigned int idx = 0; idx < objc_prop_struct->getNumOperands();
           idx++) {
        ConstantStruct *propstruct =
            dyn_cast<ConstantStruct>(objc_prop_struct->getOperand(idx));
        ;
        StringRef name =
            dyn_cast<ConstantDataArray>(
                dyn_cast<GlobalVariable>(
                    dyn_cast<ConstantExpr>(propstruct->getOperand(0))
                        ->getOperand(0))
                    ->getInitializer())
                ->getAsString();
        StringRef attri =
            dyn_cast<ConstantDataArray>(
                dyn_cast<GlobalVariable>(
                    dyn_cast<ConstantExpr>(propstruct->getOperand(1))
                        ->getOperand(0))
                    ->getInitializer())
                ->getAsString();
        propList.push_back(make_tuple(name, attri));
      }
    }
    // TODO: Now use IRB to add props and ivars
    // Parse PropertyString using
    // https://developer.apple.com/library/content/documentation/Cocoa/Conceptual/ObjCRuntimeGuide/Articles/ocrtPropertyIntrospection.html

    for (tuple<GlobalVariable * /*ivarOffsetGV*/, StringRef /*IVAR NAME*/,
               StringRef /*ivar type*/, ConstantInt * /*IVAR SIZE*/>
             tup : ivarList) {
      Value *IvarNamePtr = IRB.CreateGlobalStringPtr(get<1>(tup));
      Value *IvarTypePtr = IRB.CreateGlobalStringPtr(get<2>(tup));
      vector<Value *> Args;
      Args.push_back(Cls);
      Args.push_back(IvarNamePtr);
      //Args.push_back(get<3>(tup));
      uint64_t Size=get<3>(tup)->getZExtValue();
      Args.push_back(ConstantInt::getSigned(class_addIvar->getFunctionType()->getParamType(2), Size));
      // Calculate alignment from
      // https://stackoverflow.com/questions/33184826/what-does-class-addivars-alignment-do-in-objective-c
      // Maybe use <llvm/Support/AlignOf.h> instead?
      uint64_t align = log2(get<3>(tup)->getZExtValue());
      Args.push_back(
          ConstantInt::getSigned(Type::getInt8Ty(M->getContext()), align));
      Args.push_back(IvarTypePtr);
      IRB.CreateCall(class_addIvar, ArrayRef<Value *>(Args));
    }
    for (tuple<StringRef /*PROP NAME*/, StringRef /*PROP ATTR*/> tup :
         propList) {
      // Split PropertyAttribute String and recreate a list of sub-attribute
      // strings  Copied from
      // https://stackoverflow.com/questions/14265581/parse-split-a-string-in-c-using-string-delimiter-standard-c
      vector<string> attributeList;
      string delim = ",";
      string s = get<1>(tup).str();
      auto start = 0U;
      auto end = s.find(delim);
      while (end != string::npos) {
        string substr = s.substr(start, end - start);
        attributeList.push_back(substr.substr(0, 1));
        attributeList.push_back(substr.substr(1, string::npos));
        start = end + delim.length();
        end = s.find(delim, start);
      }
      //ArrayType *propAT = ArrayType::get(Type::getInt8Ty(M->getContext()),attributeList.size());
      Value *propName = IRB.CreateGlobalStringPtr(get<0>(tup));
      vector<Constant *> stringList;
      for (string sub : attributeList) {
        Constant *GV = reinterpret_cast<Constant*>(IRB.CreateGlobalStringPtr(sub));
        stringList.push_back(GV);
      }
      errs()<<"Handling Property:"<<get<0>(tup).str()<<" with property:"<<get<1>(tup).str()<<"\n";
      // Create GEPs to build objc_property_attribute_*
      // class_addProperty(Class cls, const char *name, const
      // objc_property_attribute_t *attributes, unsigned int attributeCount);
      vector<Constant*> attributeConstants;
      for (unsigned long index = 0; index < stringList.size();
           index = index + 2) {
        vector<Constant *> List;
        List.push_back(stringList[index]);
        List.push_back(stringList[index + 1]);
        ConstantStruct *attribute = reinterpret_cast<ConstantStruct*>(ConstantStruct::get(
            objc_property_attribute_t_type,
            ArrayRef<Constant *>(List)));
        attributeConstants.push_back(attribute);
        
      }
    ArrayType* attrListType=ArrayType::get(objc_property_attribute_t_type, attributeConstants.size());
    AllocaInst* AI=IRB.CreateAlloca(attrListType);
    Constant* attrArray=ConstantArray::get(attrListType, ArrayRef<Constant*>(attributeConstants));
    GlobalVariable* GVAttrList=new GlobalVariable(*M,attrListType,true,GlobalValue::LinkageTypes::PrivateLinkage,attrArray);
    Value* attrBC=IRB.CreateBitCast(AI, Int8PtrTy);
    IRB.CreateMemCpy(attrBC, GVAttrList,M->getDataLayout().getTypeStoreSizeInBits(attrListType), 16);
        vector<Value*> CallArgs;
      CallArgs.push_back(Cls);
      CallArgs.push_back(propName);
        vector<Value*> Args;
        Args.push_back(ConstantInt::get(Int32Ty, 0));
        Args.push_back(ConstantInt::get(Int32Ty, 0));
      CallArgs.push_back(IRB.CreateInBoundsGEP(GVAttrList, ArrayRef<Value*>(Args)));
      CallArgs.push_back(ConstantInt::get( Int32Ty,attributeConstants.size()));
      IRB.CreateCall(class_addProperty,ArrayRef<Value*>(CallArgs));
    }

    IRB.CreateCall(objc_registerClassPair, {Cls});
  }
  StringRef getPassName() const override { return "AntiClassDump"; }

}; // struct
Pass *createAntiClassDump() { return new AntiClassDump(); }
} // namespace llvm

char AntiClassDump::ID = 0;
