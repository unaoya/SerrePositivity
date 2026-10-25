module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawData
/-!
概要：逆構成した全混合成分を、任意のパラメーター係数と実 native 列の合成で計算する。
方針：矩形の左右への分割を消し、部分単体の次数を指定次数へ比較する。
規約：入力は任意の線形成分族で、HA 方程式を仮定しない。
使われ方：逆構成の元の単体側の HA 項の因数分解。
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

lemma dgCoherentBarInverseRawData_mixed_hom_heq {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1)))
    (hK : K.Nonempty) (hL : L.Nonempty) (r : ℕ) (hcK : K.card = r + 1)
    (q : ℤ) (hq : q = 1 - (L.card : ℤ))
    (a b : Fin (n + m + 1 + 1)) (k : ℤ)
    (hJ : 2 ≤ (dgCoherentBarJoinSubset K L).card)
    (ha : a = (dgCoherentBarJoinSubset K L).min' (Index.nonempty hJ))
    (hb : b = (dgCoherentBarJoinSubset K L).max' (Index.nonempty hJ))
    (hk : k = 2 - ((dgCoherentBarJoinSubset K L).card : ℤ)) :
    HEq ((dgCoherentBarInverseRawData R D F hMC N f s).hom
      (dgCoherentBarJoinSubset K L) a b k hJ ha hb hk)
      (dgCoherentBarInverseMixedColumn R D F hMC N f L q hL hq
        (dgCoherentBarSubsetLabel s K r hcK)) := by
  have hRaw := dgCoherentBarJoinRawData_mixed_hom_heq
    (coherentDiagramSimplex F s).toSimplexData
    (InfinityCategories.PinchedHom.constant (X := dgNerve R (RightModule R D))
      (Simplex.vertex (A := R) N) m).toSimplexData
    (dgCoherentBarInverseMixedData R D F hMC N f s) K L hK hL a b k hJ ha hb hk
  have hr : K.card - 1 = r := by omega
  cases hr
  cases hq
  refine hRaw.trans ?_
  unfold dgCoherentBarInverseMixedData
  exact gradedHomTransport_heq (A := R) (D := RightModule R D) _ _ _ _

def dgCoherentBarInverseParameterHomAt {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (L : Finset (Fin (m + 1))) (q : ℤ) (hL : L.Nonempty)
    (hq : q = 1 - (L.card : ℤ)) (s : I _⦋n⦌) :
    GradedHom R ((dgCoherentBarNativeSimplex R D F hMC s).obj (Fin.last (n + 1))) N q :=
  gradedHomTransport (dgCoherentBarNativeSimplex_last R D F hMC s).symm rfl rfl
    (dgCoherentBarInverseParameterCoefficient f L q hL hq)

lemma dgCoherentBarInverseParameterHomAt_heq {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (L : Finset (Fin (m + 1))) (q : ℤ) (hL : L.Nonempty)
    (hq : q = 1 - (L.card : ℤ)) (s : I _⦋n⦌) :
    HEq (dgCoherentBarInverseParameterHomAt R D F hMC N f L q hL hq s)
      (dgCoherentBarInverseParameterCoefficient f L q hL hq) :=
  gradedHomTransport_heq _ _ _ _

end SerrePositivity.InfinityCategories
