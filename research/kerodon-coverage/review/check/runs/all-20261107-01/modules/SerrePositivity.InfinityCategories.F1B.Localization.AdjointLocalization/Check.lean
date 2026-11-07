import SerrePositivity.InfinityCategories.F1B.Localization.AdjointLocalization

set_option pp.universes true
set_option pp.explicit true

-- reference 59891c70807e5c18007d
#check @F1B.Localization.AdjointLocalization.isLocalization
#print axioms F1B.Localization.AdjointLocalization.isLocalization

-- reference 8a96108941784edd9c59
#check @QCatAdjunction.isLocalization
#print axioms QCatAdjunction.isLocalization
