---- MODULE ClosedImport ----
LOCAL C == INSTANCE ClosedLibrary
Result == C!Tree
Law == Result = << <<TRUE, TRUE>>, <<TRUE, TRUE>> >>
====
