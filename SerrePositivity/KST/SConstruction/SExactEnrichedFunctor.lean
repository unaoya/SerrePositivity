module
public import SerrePositivity.KST.SConstruction.SExactFamilyMap
public import SerrePositivity.KST.SConstruction.SExactFamilyCoherence
public import SerrePositivity.KST.SConstruction.ClosedRightActionComposition

/-! # 元の全 gapped S_n の厳密単体的豊穣関手
概要：元の S_n を、安定 ∞ 圏と完全関手の全 Hom を保つ厳密豊穣自己関手にする。
方針：全パラメータ作用の単位・合成保存を curry し、完全関手空間の包含で反映する。
規約：関手同型による弱い合成則で代用しない。使われ方：反復 S• と豊穣 K。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

/-- 元の全単体的 S_n 関手族は、完全関手空間の単位を厳密に保つ。 -/
lemma sExactFamilyMap_unit (n : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactIdentity C ≫ sExactFamilyMap n C C = MonoidalClosed.id (sConstruction n C.obj) := by
  apply uncurry_injective
  rw [sExactFamilyMap, uncurry_natural_left, uncurry_curry,
    MonoidalClosed.id_eq, uncurry_curry, ← id_tensorHom]
  exact sExactFamilyAction_unit n C

/-- 元の全単体的 S_n 関手族は、完全関手空間の実合成を厳密に保つ。 -/
lemma sExactFamilyMap_comp (n : ℕ) (C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    (sExactFamilyMap n C D ⊗ₘ sExactFamilyMap n D E) ≫
        MonoidalClosed.comp (sConstruction n C.obj) (sConstruction n D.obj)
          (sConstruction n E.obj) = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactComposition C D E ≫ sExactFamilyMap n C E :=
  rightActionCurry_comp _ _ _ _ (sExactFamilyAction_comp n C D E)

/-- 全 S_n 関手族の curry は、面退化の前後合成と全単体で厳密に可換する。 -/
lemma sExactFamilyMap_restriction {m n : ℕ} (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
    (θ : Fin (m + 1) →o Fin (n + 1)) :
    sExactFamilyMap n C D ≫ (ihom (sConstruction n C.obj)).map (sMap D.obj θ) =
      sExactFamilyMap m C D ≫ (pre (sMap C.obj θ)).app (sConstruction m D.obj) := by
  apply uncurry_injective
  simp only [sExactFamilyMap, uncurry_natural_right, uncurry_pre_app, uncurry_curry]
  simpa only [tensorHom_id] using sExactFamilyAction_sMap C D θ

/-- 元の全完全関手族に作用する、実 S_n の厳密単体的豊穣自己関手。 -/
def sExactEnrichedEndofunctor (n : ℕ) :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} where
  obj := sExactCategory n
  map C D := sExactEnrichedMap n C D
  map_id C := by
    ext k p
    apply Subtype.ext
    exact congrArg (fun f => f.app k p) (sExactFamilyMap_unit n C)
  map_comp C D E := by
    ext k p
    apply Subtype.ext
    exact congrArg (fun f => f.app k p) (sExactFamilyMap_comp n C D E).symm

/-- 豊穣作用は通常の元の完全射で、同じ cofiber 型 S_n 後合成を回収する。 -/
lemma sExactEnrichedEndofunctor_hom (n : ℕ) {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv F ≫ (sExactEnrichedEndofunctor n).map C D = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv (sExactMap n F) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (sExactCategory n C) (sExactCategory n D)).ι).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun g => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv F ≫ g) (sExactEnrichedMap_inclusion n C D)).trans
      ((sExactFamilyMap_fixed n F).trans (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv_ι (sExactMap n F)).symm))

end SerrePositivity.KST.SConstruction
