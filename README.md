# LLVMAntiClassDump
An LLVM PoC pass I've created a few months ago.
There might be bugs or whatsoever, who cares.

It removes all method references from the IR structs and create/re-use existing `+initialize` to dynamically add the methods
