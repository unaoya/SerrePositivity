import SerrePositivity.InfinityCategories.F1.Transport.EdgeTransport

set_option pp.universes true
set_option pp.explicit true

-- reference 384700399c718845734e
#check @IsEdgeTransport
#print axioms IsEdgeTransport

-- reference ae371b0a206158004ed2
#check @edgeTransport_isTransport
#print axioms edgeTransport_isTransport

-- reference a1645458a3c9d077c3f4
#check @IsEdgeTransport.functorIso
#print axioms IsEdgeTransport.functorIso

-- reference 7bc40ed1c5bd8735f75e
#check @edgeTransport
#print axioms edgeTransport
