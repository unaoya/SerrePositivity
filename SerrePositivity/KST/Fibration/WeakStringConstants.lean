module
public import SerrePositivity.KST.Fibration.TopClosedStableIso

/-! # 元の安定圏から全有限 W 列への定数図式の完全関手 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 零長の元の W 列を、その唯一の頂点を持つ元の安定圏へ戻す厳密同型。 -/
def weakStringZeroAmbientIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakStringModel q ⦋0⦌ ≅ sInputModel B :=
  weakStringZeroExactIso q ≪≫ topClosedStableIso (sInputModel B)

/-- 同じ零長同型の逆は、元の一点上の定数図式を全関手圏で回収する。 -/
lemma weakStringZeroAmbientIso_inv_ι {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (weakStringZeroAmbientIso q).inv.val ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q ⦋0⦌)).ι =
        (SConstruction.pointFunctorEvaluationIso B.obj).inv := by
  change ((topClosedStableIso (sInputModel B)).inv.val ≫
    (weakStringZeroExactIso q).inv.val) ≫ _ = _
  have he : (weakStringZeroExactIso q).inv.val ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q ⦋0⦌)).ι =
        (closedStableInclusion (ClosedStablePredicate.top (sInputModel B))).val ≫
          (SConstruction.pointFunctorEvaluationIso B.obj).inv := rfl
  rw [Category.assoc, he, ← Category.assoc]
  change ((topClosedStableIso (sInputModel B)).inv.val ≫
    (topClosedStableIso (sInputModel B)).hom.val) ≫ _ = _
  have ht : (topClosedStableIso (sInputModel B)).inv.val ≫
      (topClosedStableIso (sInputModel B)).hom.val = 𝟙 B.obj :=
    congrArg Subtype.val (topClosedStableIso (sInputModel B)).inv_hom_id
  rw [ht]
  rfl

/-- 零長同型の逆と元の退化から構成する、全長の定数 W 列の完全関手。 -/
def weakStringConstantExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n : SimplexCategory) : sInputModel B ⟶ weakStringModel q n :=
  (weakStringZeroAmbientIso q).inv ≫
    weakStringExactMap q (SimplexCategory.const n ⦋0⦌ 0)

/-- 定数 W 列は、全関手圏で元の定数関手そのものを回収する。 -/
@[reassoc]
lemma weakStringConstantExact_ι {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n : SimplexCategory) :
    (weakStringConstantExact q n).val ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q n)).ι =
        curry (snd (stdSimplex.obj n) B.obj) := by
  change ((weakStringZeroAmbientIso q).inv.val ≫
    weakStringMap q (SimplexCategory.const n ⦋0⦌ 0)) ≫ _ = _
  rw [Category.assoc, weakStringMap_ι, ← Category.assoc, weakStringZeroAmbientIso_inv_ι]
  change curry (snd (Δ[0] : SSet.{u}) B.obj) ≫ _ = _
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, uncurry_curry, whiskerRight_snd]

end SerrePositivity.KST.Fibration
