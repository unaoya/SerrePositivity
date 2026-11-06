import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated

set_option pp.universes true
set_option pp.explicit true

-- reference 5918d25a080c9c54f699
#check @SSet.Truncated.instCategoryHomotopyCategory₂
#print axioms SSet.Truncated.instCategoryHomotopyCategory₂

-- reference c33266fdaf8cc9f0466d
#check @SSet.Truncated.HomotopicL.refl
#print axioms SSet.Truncated.HomotopicL.refl

-- reference 11addb2093dd89518aa4
#check @SSet.Truncated.HomotopicL.symm
#print axioms SSet.Truncated.HomotopicL.symm

-- reference 46ce24213149f35e95d3
#check @SSet.Truncated.HomotopicL.trans
#print axioms SSet.Truncated.HomotopicL.trans
