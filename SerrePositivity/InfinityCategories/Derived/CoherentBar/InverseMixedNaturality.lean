module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseFullEquation
/-!
概要：逆構成の混合列は、両側の部分集合上で単射な二つの添字写像に自然である。
方針：パラメーター係数の像との比較と、元の部分単体ラベルの厳密な等式を使う。
規約：任意の線形成分族を扱い、端点を異種等号で保持する。
使われ方：逆データの単射自然性と全部分集合の HA 方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

private lemma nativeColumn_heq (p p' : dgCoherentBarIndex I) (h : p = p') :
    HEq (dgCoherentBarNativeColumn R D F hMC p)
      (dgCoherentBarNativeColumn R D F hMC p') := by
  cases h
  rfl

lemma dgCoherentBarInverseMixedColumn_reindex {a b n m : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (α : Fin (a + 1) →o Fin (n + 1))
    (β : Fin (b + 1) →o Fin (m + 1))
    (K : Finset (Fin (a + 1))) (L : Finset (Fin (b + 1)))
    (_hK : K.Nonempty) (hL : L.Nonempty)
    (hiK : Set.InjOn α (K : Set (Fin (a + 1))))
    (hiL : Set.InjOn β (L : Set (Fin (b + 1))))
    (r : ℕ) (hcK : K.card = r + 1) (q : ℤ) (hq : q = 1 - (L.card : ℤ)) :
    HEq (dgCoherentBarInverseMixedColumn R D F hMC N
      (DGNerve.PinchedHom.LinearData.pullback β f) L q hL hq
      (dgCoherentBarSubsetLabel (I.map (SimplexCategory.mkHom α).op s) K r hcK))
      (dgCoherentBarInverseMixedColumn R D F hMC N f (L.image β) q (hL.image β)
        (by rw [Finset.card_image_of_injOn hiL]; exact hq)
        (dgCoherentBarSubsetLabel s (K.image α) r
          (by rw [Finset.card_image_of_injOn hiK]; exact hcK))) := by
  have hLabel := dgCoherentBarSubsetLabel_map_of_injOn s α K hiK r hcK
  have hSource := congrArg (dgCoherentBarSource R D F) hLabel
  have hNative := nativeColumn_heq R D F hMC _ _ hLabel
  have hPhi := dgCoherentBarInverseParameterCoefficient_pullback_inj f β L q hL hq hiL
  unfold dgCoherentBarInverseMixedColumn
  exact gradedHom_compose_heq (A := R) (D := RightModule R D)
    hSource rfl rfl rfl rfl rfl
    (p := -(r : ℤ)) (q := q) (k := q - (r : ℤ))
    (p' := -(r : ℤ)) (q' := q) (k' := q - (r : ℤ))
    _ _ _ _ (heq_of_eq hPhi) hNative (by omega) (by omega)

end SerrePositivity.InfinityCategories
