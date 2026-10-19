module
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationStabilityDescent
public import SerrePositivity.InfinityCategories.Core.EquivalenceAllLimits

/-! # ∞ 圏同値による安定性と完全性の輸送

概要：任意の quasicategory の同値は安定性を保ち反映し、完全関手である。
方針：可逆 path 置換の二つの自明 Kan fibration と厳密な切断へ分解する。
規約：三角圏の構造から安定性を引き戻さない。使われ方：β3 の dg Yoneda と平坦模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]

/-- ∞ 圏同値の両端の安定性は同値。 -/
lemma IsQCatEquivalence.isStable_iff {f : X ⟶ Y} (he : IsQCatEquivalence f) :
    IsStable X ↔ IsStable Y := by
  let q := equivalencePathReplacementMap f
  have : TrivialKanFibration q := he.equivalencePathReplacementMap_trivialKanFibration
  exact (isStable_iff_of_trivialKanFibration (equivalencePathReplacementProjection f)).symm.trans
    (isStable_iff_of_trivialKanFibration q)

/-- 明示的な ∞ 圏同値の両端の安定性は同値。 -/
lemma QCatEquivalence.isStable_iff (e : QCatEquivalence X Y) : IsStable X ↔ IsStable Y :=
  e.isQCatEquivalence.isStable_iff

/-- 任意の ∞ 圏同値は零対象と cofiber 列を保存する完全関手。 -/
lemma isExactFunctor_of_isQCatEquivalence {f : X ⟶ Y} (he : IsQCatEquivalence f) :
    IsExactFunctor f := by
  let q := equivalencePathReplacementMap f
  have : TrivialKanFibration q := he.equivalencePathReplacementMap_trivialKanFibration
  let s := equivalencePathReplacementSection f
  have : IsExactFunctor s := isExactFunctor_section_of_trivialKanFibration
    (equivalencePathReplacementProjection f) s (equivalencePathReplacementSection_projection f)
  have h : IsExactFunctor (s ≫ q) := inferInstance
  simpa only [s, q, equivalencePathReplacementSection_map] using h

end SerrePositivity.InfinityCategories
