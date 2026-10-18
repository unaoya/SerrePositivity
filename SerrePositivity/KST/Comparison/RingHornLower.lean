module

public import SerrePositivity.KST.Comparison.RingHornFaces

/-!
# ホーンの低い面からの有限回の補正

概要：欠けた面より前の全ての指定面を加法と退化で順に合わせる。
方針：一つの面を補正し、互換性による零の誤差の面でそれ以前の面を保つ。
規約：KST Lemma 2.13 の加法群の Kan 性の構成の前半。
使われ方：高い面からの補正の初期値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite
open scoped Simplicial

/--
概要：一つの低い面を合わせても、それ以前の指定面は保持される。
方針：退化の補正で新しい面を合わせ、共通の面の互換性で以前の面の誤差を零にする。
規約：欠けた面には値を指定しない。
使われ方：低い面の有限帰納の一段。
-/
theorem RingHornFaces.correct_lower_step (A : SimplicialObject RingCat.{u}) {n : ℕ}
    {k : Fin (n + 3)} (F : RingHornFaces A n k) (y : A.obj (op ⦋n + 2⦌))
    (i : Fin (n + 2)) (hi : i.castSucc ≠ k)
    (hy : ∀ (j : Fin (n + 3)) (hj : j ≠ k), j < i.castSucc →
      (A.δ j).hom y = F.face j hj) :
    ∀ (j : Fin (n + 3)) (hj : j ≠ k), j ≤ i.castSucc →
      (A.δ j).hom (ringAddDegeneracy A y i
        (F.face i.castSucc hi - (A.δ i.castSucc).hom y)) = F.face j hj := by
  intro j hj hji
  by_cases h : j = i.castSucc
  · subst j
    exact ringAddDegeneracy_correct_lower A y i _
  · have hlt : j < i.castSucc := lt_of_le_of_ne hji h
    have hi0 : i ≠ 0 := by
      intro hi0
      subst i
      simp at hlt
    obtain ⟨p, rfl⟩ := i.eq_succ_of_ne_zero hi0
    obtain ⟨q, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hlt)
    have hqp : q ≤ p.castSucc := by
      change q.val ≤ p.val
      change q.val < p.val + 1 at hlt
      omega
    have ht : p.castSucc.succ ≠ k := by simpa only [Fin.castSucc_succ] using hi
    have he : (A.δ q).hom
        (F.face p.succ.castSucc hi - (A.δ p.succ.castSucc).hom y) = 0 := by
      simpa only [Fin.castSucc_succ] using
        F.error_face_low A y q p.castSucc hqp hj ht (hy q.castSucc hj hlt)
    exact (ringAddDegeneracy_preserves_low A y p q hqp _ he).trans (hy q.castSucc hj hlt)

/--
概要：欠けた面より前の任意の有限個の指定面に一致する単体が存在する。
方針：零単体から始め、低い面を一つずつ補正する。
規約：m は合わせる面の個数、m≤k。
使われ方：欠けた面の直前まで合わせたホーン充填の初期値。
-/
theorem RingHornFaces.exists_lower_prefix (A : SimplicialObject RingCat.{u}) {n : ℕ}
    {k : Fin (n + 3)} (F : RingHornFaces A n k) (m : ℕ) (hm : m ≤ k.val) :
    ∃ y : A.obj (op ⦋n + 2⦌), ∀ (j : Fin (n + 3)) (hj : j ≠ k), j.val < m →
      (A.δ j).hom y = F.face j hj := by
  revert hm
  induction m with
  | zero =>
    intro _
    exact ⟨0, fun j hj h => False.elim (Nat.not_lt_zero _ h)⟩
  | succ m ih =>
    intro hm
    obtain ⟨y, hy⟩ := ih (by omega)
    have hmb : m < n + 2 := by omega
    let i : Fin (n + 2) := ⟨m, hmb⟩
    have hi : i.castSucc ≠ k := by
      intro he
      have hv := congrArg Fin.val he
      change m = k.val at hv
      omega
    let z := ringAddDegeneracy A y i (F.face i.castSucc hi - (A.δ i.castSucc).hom y)
    refine ⟨z, fun j hj h => ?_⟩
    apply F.correct_lower_step A y i hi (fun l hl hlt => hy l hl hlt) j hj
    change j.val ≤ m
    omega

end SerrePositivity.KST.Comparison
