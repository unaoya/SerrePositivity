import SerrePositivity.InfinityCategories.Core.Limit

set_option pp.universes true
set_option pp.explicit true

-- reference cb8c1737d24f77f9a92b
#check @IsLimitCone
#print axioms IsLimitCone

-- reference 886358d60f30c800d0f6
#check @HasLimit
#print axioms HasLimit

-- reference 22cc2a3e7dcb478d9fcd
#check @limitVertexIso
#print axioms limitVertexIso

-- reference 48da378157e817939924
#check @limitConeIso
#print axioms limitConeIso

-- reference 15aabe524ee3fe4845ec
#check @JoinCone
#print axioms JoinCone

-- reference d12e176ae510aaa73433
#check @isLimitCone_iff_trivialKanFibration
#print axioms isLimitCone_iff_trivialKanFibration
