# LLVMAntiClassDump
An LLVM PoC pass I've created a few months ago. **As such, you probably shouldn't considering using it in production envrionment**
There might be bugs or whatsoever, and there are definitely places for improvement, who cares.

It removes all method references from the IR structs and create/re-use existing ```+initialize``` to dynamically add the methods.
First known LLVM pass that solves this issue.
Initially planned to keep private because:

- Buggy
- Why not

However since it only requires runtime dump to defeat this ```protection```, releasing it seems to be OK


