import SerrePositivity.KST.SConstruction.FunctorPointwiseColimitExistence

set_option pp.universes true
set_option pp.explicit true

-- reference 4e0d9750721dcdb8c441
#check @hasColimit_of_hasPointwiseColimits
#print axioms hasColimit_of_hasPointwiseColimits

-- reference fd020e0f20f69cefdc53
#check @isColimitCone_iff_pointwise_of_hasPointwiseColimits
#print axioms isColimitCone_iff_pointwise_of_hasPointwiseColimits

-- reference 9b97c8402bcbdb36909b
#check @exists_pointwiseColimitCone
#print axioms exists_pointwiseColimitCone
