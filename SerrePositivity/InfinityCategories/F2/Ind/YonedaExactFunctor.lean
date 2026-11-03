module

public import SerrePositivity.InfinityCategories.F2.Ind.YonedaSquarePreservation
public import SerrePositivity.InfinityCategories.F2.Ind.YonedaZero
public import SerrePositivity.InfinityCategories.Stable.ExactFunctor
public import SerrePositivity.InfinityCategories.Core.UniverseSquareHom
public import SerrePositivity.InfinityCategories.Core.UniverseZeroObjects

/-!
概要：元の Yoneda 包含は、明示交換入力のもとで零頂点と全 cofiber 列を保存する。
方針：零頂点の宇宙反映と、元の実四角形の降下・押し出し保存を使う。
規約：完全性は Stable の既存定義。Ind の安定性を前提として循環させない。
使われ方：I-2 c の包含の完全性。C の安定性の供給後にも同じ公開界面を使う。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の Yoneda 包含は、全ての元の零頂点を零頂点へ送る。 -/
lemma indYoneda_preservesZeroVertices (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    {C : SSet.{u}} [Quasicategory C] : PreservesZeroVertices (indYoneda κ C) := by
  intro x hx
  exact indYoneda_isZero_of_zero κ hκ ((isZeroVertex_iff_ulift.{u, u + 1} x.down).mpr hx)

/-- 同じ元の Yoneda 包含は、明示交換入力のもとで完全関手である。 -/
lemma indYoneda_isExactFunctor (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hex : IndFiniteLimitExchangeInput.{u}) (C : SSet.{u}) [Quasicategory C] :
    IsExactFunctor (indYoneda κ C) where
  preservesZero := indYoneda_preservesZeroVertices κ hκ
  preservesCofiber t ht := by
    obtain ⟨L, hL⟩ := (uliftSquareHomEquiv.{u, u + 1} C).surjective t.square
    have hp : IsPushoutSquare L := by
      apply (isPushoutSquare_iff_ulift.{u, u + 1} L).mpr
      rw [show uliftSquare.{u, u + 1} L = t.square from hL]
      exact ht
    have h := indYoneda_preservesPushoutSquare κ hκ hex L hp
    rw [show uliftSquare.{u, u + 1} L = t.square from hL] at h
    exact h

end SerrePositivity.InfinityCategories.F2.Ind
