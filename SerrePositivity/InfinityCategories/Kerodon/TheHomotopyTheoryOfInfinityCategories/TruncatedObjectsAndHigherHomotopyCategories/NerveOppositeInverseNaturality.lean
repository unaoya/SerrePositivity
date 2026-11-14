module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOpposite

/-!
概要：元のnerve反転同型の逆の自然性を、同じ全写像の等式として記録する。
方針：元の順写像の自然性を同じ二つの逆と合成する。
規約：全単体と元の関手を保つ。
使われ方：全source-frame augmentationの反転を元の端点の全図式へ引き戻す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open CategoryTheory SSet

/-- 元のnerve反転同型の逆も、同じ通常関手に全自然。 -/
@[reassoc]
theorem nerveOppositeIso_inv_naturality
    {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D) :
    nerveMap F.op ≫ (nerveOppositeIso (C := D)).inv =
      (nerveOppositeIso (C := C)).inv ≫ SSet.opFunctor.map (nerveMap F) := by
  apply (cancel_mono (nerveOppositeIso (C := D)).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc]
  change nerveMap F.op = (nerveOppositeIso (C := C)).inv ≫
    (SSet.opFunctor.map (nerveMap F) ≫ (nerveOppositeMap (C := D)))
  rw [nerveOppositeMap_naturality F]
  change nerveMap F.op = (nerveOppositeIso (C := C)).inv ≫
    ((nerveOppositeIso (C := C)).hom ≫ nerveMap F.op)
  rw [Iso.inv_hom_id_assoc]
end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
