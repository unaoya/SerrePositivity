import Mathlib.Order.InitialSeg

set_option pp.universes true
set_option pp.explicit true

-- reference 0e41c1407a60a058b870
#check @InitialSeg
#print axioms InitialSeg

-- reference 4ce8dcc3fe7e3f869e74
#check @InitialSeg.le_apply_iff
#print axioms InitialSeg.le_apply_iff

-- reference 0b756af6afbcc9ddeca3
#check @InitialSeg.subsingleton_of_trichotomous_of_irrefl
#print axioms InitialSeg.subsingleton_of_trichotomous_of_irrefl

-- reference e90aa76dcfcfd88d19e0
#check @InitialSeg.total
#print axioms InitialSeg.total
