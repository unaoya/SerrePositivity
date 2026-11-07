import SerrePositivity.InfinityCategories.F1.Transport.Composition

set_option pp.universes true
set_option pp.explicit true

-- reference 3a01e81797f3a66037be
#check @IsEdgeTransport.comp
#print axioms IsEdgeTransport.comp

-- reference 6b0d5c54f1a98928a2f0
#check @edgeTransport_composition_iso
#print axioms edgeTransport_composition_iso
