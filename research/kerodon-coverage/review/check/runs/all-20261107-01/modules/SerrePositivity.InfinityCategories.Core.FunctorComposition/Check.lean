import SerrePositivity.InfinityCategories.Core.FunctorComposition

set_option pp.universes true
set_option pp.explicit true

-- reference 59a7b783b66c520ff270
#check @QCatEquivalence.postcompose
#print axioms QCatEquivalence.postcompose

-- reference 220bd3ad6ecb7968a232
#check @QCatEquivalence.precompose
#print axioms QCatEquivalence.precompose

-- reference a93c0e7a5c5199d02e76
#check @FunctorIso.map_post
#print axioms FunctorIso.map_post

-- reference 8cb7a061851e0b784dc8
#check @IsQCatEquivalence.postcompose
#print axioms IsQCatEquivalence.postcompose
