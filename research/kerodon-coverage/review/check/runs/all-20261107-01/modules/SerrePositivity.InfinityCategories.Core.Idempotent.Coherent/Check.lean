import SerrePositivity.InfinityCategories.Core.Idempotent.Coherent

set_option pp.universes true
set_option pp.explicit true

-- reference 1bd82a7017fdb9e9e36f
#check @CoherentIdempotent
#print axioms CoherentIdempotent

-- reference 59a4c9d9fbf4a9b484eb
#check @StrongSplitting
#print axioms StrongSplitting

-- reference 635856a5154e93b54ff7
#check @IsIdempotentComplete
#print axioms IsIdempotentComplete

-- reference c05bf897d7e7c42cbfa1
#check @CoherentIdempotent.endomorphism
#print axioms CoherentIdempotent.endomorphism
