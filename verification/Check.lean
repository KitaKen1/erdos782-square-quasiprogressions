module

import Comparator.Candidate

open Erdos782

-- Check the candidate against the proposition extracted directly from FC.
example : ¬ FCPartIStatement :=
  erdos_782.parts.i_neg

#check @Erdos782.erdos_782.parts.i_neg

/-- info: 'Erdos782.erdos_782.parts.i_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos782.erdos_782.parts.i_neg
