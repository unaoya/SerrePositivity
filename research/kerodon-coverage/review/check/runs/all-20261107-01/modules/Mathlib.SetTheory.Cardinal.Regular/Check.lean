import Mathlib.SetTheory.Cardinal.Regular

set_option pp.universes true
set_option pp.explicit true

-- reference 819ea9059b02d117c096
#check @Ordinal.isRegular_cof
#print axioms Ordinal.isRegular_cof

-- reference 6c6205b5b7d45a9d6c5b
#check @Cardinal.iSup_lt_of_isRegular
#print axioms Cardinal.iSup_lt_of_isRegular

-- reference 59d9988bb7a4a88b8e65
#check @Cardinal.sum_lt_of_isRegular
#print axioms Cardinal.sum_lt_of_isRegular

-- reference 50bc8e741201fa0fcf2a
#check @Cardinal.card_iUnion_lt_iff_forall_of_isRegular
#print axioms Cardinal.card_iUnion_lt_iff_forall_of_isRegular

-- reference 428fa12036dfdc149ea9
#check @Cardinal.IsRegular
#print axioms Cardinal.IsRegular

-- reference 52fcc84ad2d1d889b645
#check @Cardinal.IsInaccessible
#print axioms Cardinal.IsInaccessible

-- reference 729f0864b69a6242dca3
#check @Cardinal.isInaccessible_def
#print axioms Cardinal.isInaccessible_def
