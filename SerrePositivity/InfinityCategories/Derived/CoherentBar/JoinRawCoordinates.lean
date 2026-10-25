module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinRawGluing
/-!
概要：貼り合わせた join 単体データの全混合成分を計算する。
方針：左右への分割が元の矩形を回収することから、混合分岐の実輸送を消す。
規約：端点と次数を異種等号で保持する。
使われ方：逆比較の HA 方程式と成分復元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]

lemma dgCoherentBarJoinMixedData_component_heq {n m : ℕ}
    {s : SimplexData R C n} {t : SimplexData R C m} (f : DGCoherentBarJoinMixedData s t)
    {K K' : Finset (Fin (n + 1))} {L L' : Finset (Fin (m + 1))}
    (hKK' : K = K') (hLL' : L = L')
    (hK : K.Nonempty) (hK' : K'.Nonempty) (hL : L.Nonempty) (hL' : L'.Nonempty)
    (k : ℤ) (hk : k = 2 - (K.card : ℤ) - (L.card : ℤ))
    (hk' : k = 2 - (K'.card : ℤ) - (L'.card : ℤ)) :
    HEq (f K L hK hL k hk) (f K' L' hK' hL' k hk') := by
  cases hKK'
  cases hLL'
  rfl

lemma dgCoherentBarJoinRawData_mixed_hom_heq {n m : ℕ}
    (s : SimplexData R C n) (t : SimplexData R C m) (f : DGCoherentBarJoinMixedData s t)
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1)))
    (hK : K.Nonempty) (hL : L.Nonempty)
    (a b : Fin (n + m + 1 + 1)) (k : ℤ)
    (hJ : 2 ≤ (dgCoherentBarJoinSubset K L).card)
    (ha : a = (dgCoherentBarJoinSubset K L).min' (Index.nonempty hJ))
    (hb : b = (dgCoherentBarJoinSubset K L).max' (Index.nonempty hJ))
    (hk : k = 2 - ((dgCoherentBarJoinSubset K L).card : ℤ)) :
    HEq ((dgCoherentBarJoinRawData s t f).hom (dgCoherentBarJoinSubset K L)
      a b k hJ ha hb hk)
      (f K L hK hL k (by rw [dgCoherentBarJoinSubset_card] at hk; push_cast at hk; omega)) := by
  dsimp only [dgCoherentBarJoinRawData]
  simp only [dgCoherentBarJoinLeftPart_subset, dgCoherentBarJoinRightPart_subset,
    dite_eq_left hK, dite_eq_left hL]
  exact (gradedHomTransport_heq (A := R) (D := C) _ _ _ _).trans
    (dgCoherentBarJoinMixedData_component_heq f
      (dgCoherentBarJoinLeftPart_subset K L) (dgCoherentBarJoinRightPart_subset K L)
      _ hK _ hL k _ _)

end SerrePositivity.InfinityCategories
