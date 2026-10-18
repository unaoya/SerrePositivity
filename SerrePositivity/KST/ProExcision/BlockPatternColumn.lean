module
public import SerrePositivity.KST.ProExcision.IntegerUnitization

/-!
# 補助列を実三角ブロック群へ制限する

概要：許される行と列、イデアル内の係数を持つ補助列は実ブロック群に入る。
方針：単一成分行列と有限和で部分環の所属を示し、逆 1−V の所属も確認する。
規約：KST Lemma 4.16 の ψ、非可換な単位化模型。
使われ方：μ 版 A.5 の第二因子 Q→H を具体的な三角ブロック群に値を持たせる。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：許される一成分を持つ行列は三角ブロック部分環に入る。
方針：その一成分以外が零であることを使う。
規約：KST 4.16、係数は両側イデアル内。
使われ方：補助列の有限和の各項の所属。 -/
lemma single_mem_blockPattern (N n : ℕ) (J : TwoSidedIdeal R)
    (i j : Fin N) (x : R) (hij : i < j ∧ n ≤ j.val) (hx : x ∈ J) :
    Matrix.single i j x ∈ blockPatternSubring N n J := by
  constructor
  · intro k l hkl
    by_cases h : i = k ∧ j = l
    · rcases h with ⟨rfl, rfl⟩
      exact (hkl hij).elim
    · exact Matrix.single_apply_of_ne _ _ _ _ _ h
  · intro k l
    by_cases h : i = k ∧ j = l
    · rcases h with ⟨rfl, rfl⟩
      simpa only [Matrix.single_apply_same] using hx
    · rw [Matrix.single_apply_of_ne _ _ _ _ _ h]
      exact J.zero_mem

/-- 概要：許される補助列でイデアル内の係数を持つ列行列は部分環に入る。
方針：一成分行列の有限和の所属を使う。
規約：KST 4.16、行 r_i は補助列 p より前にある。
使われ方：実群 H 内に値を持つ ψ の構成。 -/
lemma blockColumn_mem_blockPattern {ι : Type v} [Fintype ι]
    (N n : ℕ) (J : TwoSidedIdeal R) (r : ι → Fin N) (p : Fin N) (v : ι → R)
    (hr : ∀ i, r i < p) (hp : n ≤ p.val) (hv : ∀ i, v i ∈ J) :
    blockColumn r p v ∈ blockPatternSubring N n J := by
  apply (blockPatternSubring N n J).sum_mem
  intro i _
  exact single_mem_blockPattern N n J (r i) p (v i) ⟨hr i, hp⟩ (hv i)

/-- 概要：部分環内の二乗零元による単位は差の部分群に入る。
方針：単位の差は V、逆の差は −V。
規約：KST 4.16、明示的な逆 1−V を使う。
使われ方：実補助列の単位群を三角ブロック群に制限する。 -/
lemma squareZeroUnit_mem_oneDifference (S : NonUnitalSubring R) (V : R)
    (hV : V * V = 0) (hmem : V ∈ S) :
    squareZeroUnit V hV ∈ oneDifferenceSubgroup S := by
  constructor
  · change 1 + V - 1 ∈ S
    simpa only [add_sub_cancel_left] using hmem
  · change (1 - V) - 1 ∈ S
    have h : (1 - V) - 1 = -V := by abel
    rw [h]
    exact S.neg_mem hmem

/-- 概要：許される補助列の単位は実三角ブロック群に入る。
方針：列の部分環所属と二乗零の単位の所属を合成する。
規約：KST Lemma 4.16 の ψ、係数環を可換と仮定しない。
使われ方：μ の第二因子の値域 H を具体的に指定する。 -/
lemma blockColumnHom_mem_triangularBlockGroup {ι : Type v} [Fintype ι]
    (n m : ℕ) (J : TwoSidedIdeal R) (r : ι → Fin (n + m)) (p : Fin (n + m))
    (hr : ∀ i, r i < p) (hp : n ≤ p.val) (v : Multiplicative (ι → R))
    (hv : ∀ i, v.toAdd i ∈ J) :
    blockColumnHom r p (fun i ↦ (hr i).ne') v ∈ triangularBlockGroup n m J := by
  exact squareZeroUnit_mem_oneDifference (blockPatternSubring (n + m) n J)
    (blockColumn r p v.toAdd) (blockColumn_square_zero r p v.toAdd (fun i ↦ (hr i).ne'))
    (blockColumn_mem_blockPattern (n + m) n J r p v.toAdd hr hp hv)

end SerrePositivity.KST.ProExcision
