module

public import SerrePositivity.HomotopicalAlgebra.Monoidal.BifunctorTransport

/-! # Localizing both tensor variables using a commutor

A Quillen bifunctor with only its second source variable changed becomes
Quillen in both changed variables if cofibrations agree and a natural
commutor identifies it with its flip. No weak-equivalence comparison in
the unchanged first variable is required.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Quillen
variable {C : Type u} [Category.{v} C] (old m : ModelCategory C) {F : C ⥤ C ⥤ C}

lemma isQuillenBifunctor_change_both_of_commutor
    (hc : m.categoryWithCofibrations.cofibrations = old.categoryWithCofibrations.cofibrations)
    (e : F ≅ F.flip)
    (hF : @IsQuillenBifunctor C _ old C _ m C _ m F) :
    @IsQuillenBifunctor C _ m C _ m C _ m F := by
  have hflip := @isQuillenBifunctor_of_natIso C C C _ _ _ old m m F F.flip e hF
  let := m
  refine @IsQuillenBifunctor.mk C _ m C _ m C _ m F ?_ ?_
  · intro A B X Y i j sq hi hj
    have hiOld : @Cofibration C _ A B i old.categoryWithCofibrations :=
      (@cofibration_iff C _ A B i old.categoryWithCofibrations).mpr
        (hc.le _ ((cofibration_iff _).mp hi))
    exact @IsQuillenBifunctor.cofibration C _ old C _ m C _ m F hF A B X Y i j sq hiOld hj
  · intro A B X Y i j sq hi hj hw
    rcases hw with hiw | hjw
    · have hjOld : @Cofibration C _ X Y j old.categoryWithCofibrations :=
        (@cofibration_iff C _ X Y j old.categoryWithCofibrations).mpr
          (hc.le _ ((cofibration_iff _).mp hj))
      exact @IsQuillenBifunctor.weakEquivalence C _ old C _ m C _ m F.flip hflip
        X Y A B j i sq.flip hjOld hi (Or.inr hiw)
    · have hiOld : @Cofibration C _ A B i old.categoryWithCofibrations :=
        (@cofibration_iff C _ A B i old.categoryWithCofibrations).mpr
          (hc.le _ ((cofibration_iff _).mp hi))
      exact @IsQuillenBifunctor.weakEquivalence C _ old C _ m C _ m F hF
        A B X Y i j sq hiOld hj (Or.inr hjw)

end SerrePositivity.Quillen
