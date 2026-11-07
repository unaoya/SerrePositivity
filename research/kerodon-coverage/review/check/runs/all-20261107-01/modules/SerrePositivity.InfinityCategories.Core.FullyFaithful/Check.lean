import SerrePositivity.InfinityCategories.Core.FullyFaithful

set_option pp.universes true
set_option pp.explicit true

-- reference d7e547bc83efd5a6acbe
#check @IsEssentiallySurjective
#print axioms IsEssentiallySurjective

-- reference f861e9c706dd7a1e1154
#check @isEssentiallySurjective_iff_hoFunctor
#print axioms isEssentiallySurjective_iff_hoFunctor

-- reference d5617b012b6bf5f0fd69
#check @IsEssentiallySurjective.comp
#print axioms IsEssentiallySurjective.comp

-- reference 336085e9336824925034
#check @IsFullyFaithful
#print axioms IsFullyFaithful

-- reference 6c76b163f1d20927dff5
#check @IsFullyFaithful.toHoFullyFaithful
#print axioms IsFullyFaithful.toHoFullyFaithful
