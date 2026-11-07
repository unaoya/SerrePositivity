import SerrePositivity.KST.SConstruction.FunctorPointwiseColimits

set_option pp.universes true
set_option pp.explicit true

-- reference 6587f25da36b21109235
#check @IsPointwiseColimitCone
#print axioms IsPointwiseColimitCone

-- reference 01a540838718f4a6524b
#check @initialBoundaryLifting_coconeRestriction_of_pointwise
#print axioms initialBoundaryLifting_coconeRestriction_of_pointwise

-- reference d1c062e1f1bea17ce9fc
#check @isColimitCone_of_pointwise
#print axioms isColimitCone_of_pointwise
