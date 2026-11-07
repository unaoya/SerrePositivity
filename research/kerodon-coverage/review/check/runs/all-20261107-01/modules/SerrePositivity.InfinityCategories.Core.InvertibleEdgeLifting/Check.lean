import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting

set_option pp.universes true
set_option pp.explicit true

-- reference a460e4e24309c2216bc4
#check @SerrePositivity.InfinityCategories.IsInvertibleEdge
#print axioms SerrePositivity.InfinityCategories.IsInvertibleEdge

-- reference b840a8bc66b8c69e8f33
#check @SerrePositivity.InfinityCategories.IsInvertibleEdge.nonempty_inverse
#print axioms SerrePositivity.InfinityCategories.IsInvertibleEdge.nonempty_inverse

-- reference 2b2545c4592859879064
#check @hasFinalHornFillers_of_isInvertibleEdge
#print axioms hasFinalHornFillers_of_isInvertibleEdge

-- reference 441b644a9c3b31a1233f
#check @IsInvertibleEdge
#print axioms IsInvertibleEdge

-- reference bd87d752dbb257bd1b5f
#check @leftFibration_reflects_invertibleEdge
#print axioms leftFibration_reflects_invertibleEdge
