---- MODULE ToolDefinitions ----
EXTENDS TLC, Randomization, Toolbox
Printed == Print("hello", 42)
PrintedTrue == PrintT("hello")
Asserted == Assert(TRUE, "ok")
Clock == JavaTime
Read == TLCGet("level")
Write == TLCSet(1, 2)
Arbitrary == Any
Text == ToString(42)
Evaluated == TLCEval(42)
Subset == RandomSubset(1, {1,2})
Subsets == RandomSetOfSubsets(1, 1, {1,2})
Samples == TestRandomSetOfSubsets(1, 1, {1,2})
Trace == _TETrace
Position == _TEPosition
====
