module

public import SerrePositivity.InfinityCategories.F2.Idempotent.IdemUniverse
public import SerrePositivity.InfinityCategories.F2.Idempotent.StrongSplittingExistence
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LimitColimitOpposite
public import SerrePositivity.InfinityCategories.Core.UniverseLimits
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration

/-!
概要：元の coherent 冪等完備性は宇宙変更で保存・反映される。
方針：全 Idem の厳密な宇宙比較で元の図式を移し、同じ余極限の保存・反映を使う。
規約：大きい宇宙の任意の全 Idem 図式を扱い、固定された小さい図式だけに制限しない。
使われ方：前層圏を通す冪等完備な標的への延長の宇宙整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の coherent 冪等完備性は、任意の大きい宇宙への持ち上げで保存される。 -/
lemma IsIdempotentComplete.ulift {X : SSet.{u}} [Quasicategory X]
    (hX : IsIdempotentComplete X) :
    IsIdempotentComplete ((SSet.uliftFunctor.{v, u}).obj X) := by
  intro d
  let a := (idemShapeUniverseIso.{u, v}).hom ≫ d
  let d₀ := (SSet.uliftFunctor.{v, u}).preimage a
  have h₀ : HasColimit ((SSet.uliftFunctor.{v, u}).map d₀) :=
    (hasColimit_iff_ulift d₀).mp (hX.hasColimit d₀)
  have ha : HasColimit a := by
    simpa only [d₀, Functor.map_preimage] using h₀
  have hd : HasColimit d :=
    (F1B.kanHasColimit_iff_restrict_of_isIso d (idemShapeUniverseIso.{u, v}).hom).mpr ha
  exact strongSplitting_exists_of_hasColimit d hd

/-- 持ち上げた ∞ 圏の coherent 冪等完備性は、元の宇宙へ反映される。 -/
lemma isIdempotentComplete_of_ulift {X : SSet.{u}} [Quasicategory X]
    (hX : IsIdempotentComplete ((SSet.uliftFunctor.{v, u}).obj X)) :
    IsIdempotentComplete X := by
  intro d
  let e := idemShapeUniverseIso.{u, v}
  let a := e.inv ≫ (SSet.uliftFunctor.{v, u}).map d
  have ha := hX.hasColimit a
  have h₀ := (F1B.kanHasColimit_iff_restrict_of_isIso a e.hom).mp ha
  have h₁ : HasColimit ((SSet.uliftFunctor.{v, u}).map d) := by
    simpa only [a, e.hom_inv_id_assoc] using h₀
  exact strongSplitting_exists_of_hasColimit d ((hasColimit_iff_ulift d).mpr h₁)

/-- coherent な元の冪等完備性は、宇宙の持ち上げで保存・反映される。 -/
lemma isIdempotentComplete_iff_ulift (X : SSet.{u}) [Quasicategory X] :
    IsIdempotentComplete X ↔ IsIdempotentComplete ((SSet.uliftFunctor.{v, u}).obj X) :=
  ⟨IsIdempotentComplete.ulift, isIdempotentComplete_of_ulift⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
