import SerrePositivity.InfinityCategories.HomotopyLimits.BousfieldKanCoherentColimit

set_option pp.universes true
set_option pp.explicit true

-- reference 361c3725116ed998bb3f
#check @HomotopyLimits.bousfieldKanCoherentCocone_isColimit
#print axioms HomotopyLimits.bousfieldKanCoherentCocone_isColimit

-- reference 62b5db15b436c3b70c96
#check @HomotopyLimits.kanDiagramCoherentNerve_hasColimit
#print axioms HomotopyLimits.kanDiagramCoherentNerve_hasColimit

-- reference b0ceeaceddad67e46f81
#check @bousfieldKanCoherentCocone_isColimit
#print axioms bousfieldKanCoherentCocone_isColimit

-- reference 2decab2761c49b962a4a
#check @kanDiagramCoherentNerve_hasColimit
#print axioms kanDiagramCoherentNerve_hasColimit
