import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

set_option pp.universes true
set_option pp.explicit true

-- reference a46f8d4e3fdf3149036f
#check @SSet.skeleton
#print axioms SSet.skeleton

-- reference dbffd3d2b16ce49113ec
#check @SSet.mem_skeleton_obj_iff_of_nonDegenerate
#print axioms SSet.mem_skeleton_obj_iff_of_nonDegenerate

-- reference 06c7c90d210765884f93
#check @SSet.skeleton_obj_eq_top
#print axioms SSet.skeleton_obj_eq_top

-- reference c9b138c684e73e3c388b
#check @SSet.ofSimplex_le_skeleton
#print axioms SSet.ofSimplex_le_skeleton

-- reference 251722d47946af71bfa5
#check @SSet.Subcomplex.Skeleton.isPushout
#print axioms SSet.Subcomplex.Skeleton.isPushout

-- reference 4014a62afaf8c528d133
#check @SSet.relativeCellComplexOfMono
#print axioms SSet.relativeCellComplexOfMono
