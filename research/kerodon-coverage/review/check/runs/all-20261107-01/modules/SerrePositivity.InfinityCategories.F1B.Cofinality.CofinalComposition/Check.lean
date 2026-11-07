import SerrePositivity.InfinityCategories.F1B.Cofinality.CofinalComposition

set_option pp.universes true
set_option pp.explicit true

-- reference e19559985fe9d2a1b317
#check @IsLeftCofinal.comp
#print axioms IsLeftCofinal.comp

-- reference d5c301b927652caee2d2
#check @IsLeftCofinal.cancel_left
#print axioms IsLeftCofinal.cancel_left

-- reference 21af3a5d4f7c89725c72
#check @IsRightCofinal.cancel_left
#print axioms IsRightCofinal.cancel_left

-- reference b45afe326439909aa1f1
#check @IsRightCofinal.comp
#print axioms IsRightCofinal.comp
