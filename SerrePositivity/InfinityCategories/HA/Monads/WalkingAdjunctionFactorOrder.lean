module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionCutRank
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionVertices

/-!
概要：同じ全単体の水平分解を全頂点の左因子の長さで比較する。
方針：元の合成の等式に沿って切れ目を移し、順位の全順序を使う。
規約：切れ目から短い因子を回収する構成とは分ける。
使われ方：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子的な分解の一意性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：指定した同じ全単体の実際の水平分解。
方針：中点と左右の実関手と、その合成の等式を記録する。
規約：全ての射の等式を持つ。使われ方：Riehl–Verity Proposition 3.1.10。 -/
structure WalkingAdjunctionFactorization {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) where
  middle : WalkingAdjunctionPoint
  left : Fin (n + 1) ⥤ walkingAdjunctionHom X middle
  right : Fin (n + 1) ⥤ walkingAdjunctionHom middle Y
  fac : left.prod' right ⋙ walkingAdjunctionHorizontal X middle Y = H

variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

/-- 概要：分解の元の合成の単体における切れ目。
方針：実分解から構成した二種類の切れ目を使う。
規約：中点を保持する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
def WalkingAdjunctionFactorization.sourceCut (a : WalkingAdjunctionFactorization H) :
    WalkingAdjunctionCut
      (a.left.prod' a.right ⋙ walkingAdjunctionHorizontal X a.middle Y) a.middle := by
  rcases a with ⟨M, L, R, h⟩
  cases M
  · exact walkingAdjunctionPlusFactorCut X Y L R
  · exact walkingAdjunctionMinusFactorCut X Y L R

/-- 概要：同じ指定単体Hに移した分解の切れ目。
方針：元の合成の等式に沿ってデータを輸送する。
規約：全射の可換条件も移す。使われ方：Riehl–Verity Proposition 3.1.10。 -/
def WalkingAdjunctionFactorization.cut (a : WalkingAdjunctionFactorization H) :
    WalkingAdjunctionCut H a.middle :=
  walkingAdjunctionCutTransport a.fac a.middle a.sourceCut

/-- 概要：分解の切れ目の順位は左因子の長さと始点の補正で決まる。
方針：plusは点の個数、minusは入る区間の次元と重みの比較を使う。
規約：中点を場合分けする。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma WalkingAdjunctionFactorization.sourceCut_rank (a : WalkingAdjunctionFactorization H)
    (i : Fin (n + 1)) :
    walkingAdjunctionCutRank a.sourceCut i =
      walkingAdjunctionVertexLength X a.middle (a.left.obj i) +
        walkingAdjunctionTargetCorrection X := by
  rcases a with ⟨M, L, R, h⟩
  cases M
  · change 2 * walkingAdjunctionOrdinalCard X .plus (L.obj i) + 0 =
      walkingAdjunctionVertexLength X .plus (L.obj i) + walkingAdjunctionTargetCorrection X
    have h₁ := walkingAdjunctionOrdinalCard_weight X .plus (L.obj i)
    have h₂ := walkingAdjunctionVertexLength_weight X .plus (L.obj i)
    change walkingAdjunctionOrdinalCard X .plus (L.obj i) =
      walkingAdjunctionWeight X .plus (L.obj i) + 0 at h₁
    change walkingAdjunctionVertexLength X .plus (L.obj i) + walkingAdjunctionTargetCorrection X =
      2 * walkingAdjunctionWeight X .plus (L.obj i) + 0 at h₂
    omega
  · change 2 * walkingAdjunctionIncomingDim X (L.obj i) + 1 =
      walkingAdjunctionVertexLength X .minus (L.obj i) + walkingAdjunctionTargetCorrection X
    rw [walkingAdjunctionIncomingDim_weight]
    exact (walkingAdjunctionVertexLength_weight X .minus (L.obj i)).symm

/-- 概要：指定単体へ移した切れ目の順位も、元の左因子の長さを保持する。
方針：順位の輸送の法則を使う。規約：同じH上で照合する。
使われ方：Riehl–Verity Proposition 3.1.10 の二つの分解の比較。 -/
lemma WalkingAdjunctionFactorization.cut_rank (a : WalkingAdjunctionFactorization H)
    (i : Fin (n + 1)) :
    walkingAdjunctionCutRank a.cut i =
      walkingAdjunctionVertexLength X a.middle (a.left.obj i) +
        walkingAdjunctionTargetCorrection X := by
  rw [WalkingAdjunctionFactorization.cut, walkingAdjunctionCutRank_transport]
  exact a.sourceCut_rank i

/-- 概要：同じ単体の任意の二つの水平分解の左因子は、全頂点で一貫して比較できる。
方針：同じH上の切れ目の順位の比較から、始点の共通の補正を除く。
規約：比較の向きは全頂点で同じ。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma WalkingAdjunctionFactorization.prefix_total (a b : WalkingAdjunctionFactorization H) :
    (∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) ∨
    (∀ i, walkingAdjunctionVertexLength X b.middle (b.left.obj i) ≤
      walkingAdjunctionVertexLength X a.middle (a.left.obj i)) := by
  rcases walkingAdjunctionCutRank_total a.cut b.cut with h | h
  · exact Or.inl (fun i => by
      have hi := h i
      rw [a.cut_rank i, b.cut_rank i] at hi
      omega)
  · exact Or.inr (fun i => by
      have hi := h i
      rw [b.cut_rank i, a.cut_rank i] at hi
      omega)

/-- 概要：左因子の全頂点の長さが同じなら二つの分解の中点は同じ。
方針：長さと重みの比較の偶奇を使う。
規約：始点の補正は共通。使われ方：Riehl–Verity Proposition 3.1.10 の等しい切れ目。 -/
lemma WalkingAdjunctionFactorization.middle_eq_of_length (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) =
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) : a.middle = b.middle := by
  rcases a with ⟨M, L, R, ha⟩
  rcases b with ⟨N, L', R', hb⟩
  have h₀ := h 0
  have h₁ := walkingAdjunctionVertexLength_weight X M (L.obj 0)
  have h₂ := walkingAdjunctionVertexLength_weight X N (L'.obj 0)
  cases M <;> cases N
  · rfl
  · change walkingAdjunctionVertexLength X .plus (L.obj 0) =
      walkingAdjunctionVertexLength X .minus (L'.obj 0) at h₀
    simp only [walkingAdjunctionTargetCorrection] at h₁ h₂
    omega
  · change walkingAdjunctionVertexLength X .minus (L.obj 0) =
      walkingAdjunctionVertexLength X .plus (L'.obj 0) at h₀
    simp only [walkingAdjunctionTargetCorrection] at h₁ h₂
    omega
  · rfl

/-- 概要：同じ単体の水平分解は、左因子の全頂点の長さで区別できる。
方針：中点と左右の対象を回収し、全水平合成の忠実性で全関手を回収する。
規約：合成の証明も含めた実データの等式。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma WalkingAdjunctionFactorization.ext_prefix_length (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) =
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) : a = b := by
  have hM := a.middle_eq_of_length b h
  rcases a with ⟨M, L, R, ha⟩
  rcases b with ⟨N, L', R', hb⟩
  change M = N at hM
  subst N
  have hL (i : Fin (n + 1)) : L.obj i = L'.obj i :=
    walkingAdjunctionVertexLength_injective X M (h i)
  have hc := ha.trans hb.symm
  have hR (i : Fin (n + 1)) : R.obj i = R'.obj i := by
    apply walkingAdjunctionWeight_injective M Y
    have hw := congrArg (walkingAdjunctionWeight X Y) (CategoryTheory.Functor.congr_obj hc i)
    simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.prod'_obj,
      walkingAdjunctionHorizontal_weight] at hw
    have hl := congrArg (walkingAdjunctionWeight X M) (hL i)
    omega
  obtain ⟨hL', hR'⟩ := walkingAdjunctionHorizontal_functor_inj X M Y L L' R R' hL hR hc
  subst L'
  subst R'
  rfl

end SerrePositivity.InfinityCategories.HA.Monads
