import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

set_option pp.universes true
set_option pp.explicit true

-- reference 4cbf41ab126116b4628e
#check @SSet.degenerate
#print axioms SSet.degenerate

-- reference 24f09c0a4130cfbd7375
#check @SSet.nonDegenerate
#print axioms SSet.nonDegenerate

-- reference 7f98c087ee3586658351
#check @SSet.degenerate_zero
#print axioms SSet.degenerate_zero

-- reference 2587e5896b59b536f64d
#check @SSet.mem_degenerate_iff
#print axioms SSet.mem_degenerate_iff

-- reference 8202e69032741faea4ed
#check @SSet.degenerate_eq_iUnion_range_σ
#print axioms SSet.degenerate_eq_iUnion_range_σ

-- reference 90cc8ee2d1393bed8213
#check @SSet.exists_nonDegenerate
#print axioms SSet.exists_nonDegenerate

-- reference 1ebef155602fc967b310
#check @SSet.unique_nonDegenerate_map
#print axioms SSet.unique_nonDegenerate_map

-- reference 4525c7b871fc7d9e3b53
#check @SSet.unique_nonDegenerate_simplex
#print axioms SSet.unique_nonDegenerate_simplex

-- reference dfa01125d74fa9fb66a5
#check @SSet.Subcomplex.le_iff_contains_nonDegenerate
#print axioms SSet.Subcomplex.le_iff_contains_nonDegenerate
