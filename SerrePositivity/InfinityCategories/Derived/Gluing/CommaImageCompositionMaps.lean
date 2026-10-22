module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaImageProjections
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaComposition

/-! 標的恒等 comma への写像は、二比較 primitive の同じ実係数合成を保存する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : DGFunctorCommaObject R C E F)
local notation "IX" => dgGluingCommaImageObject R C E F X
local notation "IY" => dgGluingCommaImageObject R C E F Y
local notation "IZ" => dgGluingCommaImageObject R C E F Z
local notation "aXY" => dgGluingCommaImageHomMap R C E F X Y
local notation "aYZ" => dgGluingCommaImageHomMap R C E F Y Z

omit X in
lemma dgGluingCommaImageHomMap_image :
    aYZ ≫ dgFunctorCommaImageHomMap R E E (DGFunctor.id E) IY IZ =
      dgFunctorCommaImageHomMap R C E F Y Z := by
  change aYZ ≫ (dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) IY IZ ≫ 𝟙 _) = _
  rw [Category.comp_id, dgGluingCommaImageHomMap_source]

lemma dgGluingCommaImageFirstCompositionMap :
    (𝟙 (homObject R E X.replacement (F.obj Y.source)) ⊗ₘ aYZ) ≫
      dgFunctorCommaFirstCompositionMap R E E (DGFunctor.id E) IX IY IZ =
      dgFunctorCommaFirstCompositionMap R C E F X Y Z := by
  simp only [dgFunctorCommaFirstCompositionMap, ← Category.assoc, tensorHom_comp_tensorHom,
    Category.id_comp]
  simp only [dgGluingCommaImageHomMap_image]
  rfl

lemma dgGluingCommaImageSecondCompositionMap :
    (aXY ⊗ₘ 𝟙 (homObject R E Y.replacement (F.obj Z.source))) ≫
      dgFunctorCommaSecondCompositionMap R E E (DGFunctor.id E) IX IY IZ =
      dgFunctorCommaSecondCompositionMap R C E F X Y Z := by
  simp only [dgFunctorCommaSecondCompositionMap, ← Category.assoc, tensorHom_comp_tensorHom,
    Category.id_comp]
  simp only [dgGluingCommaImageHomMap_replacement]
  rfl

end SerrePositivity.InfinityCategories
