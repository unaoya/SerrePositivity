module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismPairing

/-!
概要：最初の外側ホーンと標準単体の積の pairing の最初の辺。
方針：pairing の垂直な一歩と右の射影の全射性を使う。
規約：左因子は次元二以上、欠けるホーンの面は零。
使われ方：Kerodon §5.3.7（Tag 01US） の錐の制限の cocartesian な辺の充填。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：ホーンと標準単体の積の最初の指定辺。
方針：左の最初の辺と右の最初の頂点の定値辺を組にする。
規約：左因子は Δ[m+2]。
使われ方：Kerodon §5.3.7（Tag 01US） の外側ホーンを埋める可逆な辺。 -/
def initialHornProductFirstEdge (m n : ℕ) :
    ((Δ[m + 2] : SSet.{u}) ⊗ Δ[n]) _⦋1⦌ :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge m).val, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) 1⟩

/-- 概要：積の最初の指定辺はホーンと境界の積の和に属する。
方針：左成分は元の最初のホーンに属する。
規約：右因子が零次元でもよい。
使われ方：Kerodon §5.3.7（Tag 01US） の既存部分上の辺の固定。 -/
lemma initialHornProductFirstEdge_mem (m n : ℕ) :
    initialHornProductFirstEdge.{u} m n ∈
      (Subcomplex.unionProd (horn (m + 2) 0) (boundary n)).obj (Opposite.op ⦋1⦌) := by
  rw [Subcomplex.mem_unionProd_iff]
  exact Or.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge m).property

/-- 概要：積の pairing の最初の右頂点は零。
方針：右射影の全射性と単調性で零を取ることを示す。
規約：左ホーンの欠ける面は零。
使われ方：Kerodon §5.3.7（Tag 01US） の外側ホーンの最初の辺の識別。 -/
lemma initialHornProductPairing_first_right_zero (m n : ℕ)
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin (m + 2)) n) :
    (s.x.cast s.hd).simplex.2 (0 : Fin (s.d + 2)) = 0 := by
  obtain ⟨i, hi⟩ := prodStdSimplex.pairingCore.mem_range_right s.x s.hd
    (0 : Fin (n + 1))
  apply le_antisymm _ (Fin.zero_le _)
  have h := stdSimplex.monotone_apply (s.x.cast s.hd).simplex.2 (Fin.zero_le i)
  exact h.trans (le_of_eq hi)

/-- 概要：最初の面で対になる積の単体の最初の辺は指定した積の辺。
方針：pairing の一歩の条件と右の最初の値の零性を計算する。
規約：右の最初の頂点で左の零頂点と一頂点を結ぶ。
使われ方：Kerodon §5.3.7（Tag 01US） の可逆な辺を含む最初の外側ホーン。 -/
lemma initialHornProductPairing_firstEdge_eq (m n : ℕ)
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin (m + 2)) n) (hi : s.index = 0) :
    ((Δ[m + 2] : SSet.{u}) ⊗ Δ[n]).map
      (stdSimplex.objEquiv (stdSimplex.edge.{u} (s.d + 1) 0 1 (Fin.zero_le _))).op
        (s.x.cast s.hd).simplex = initialHornProductFirstEdge m n := by
  have h := (prodStdSimplex.pairingCore.isIndex_succ s.x s.hd s.index).1 s.isIndex
  rw [hi] at h
  apply Prod.ext
  · apply stdSimplex.ext
    intro i
    fin_cases i
    · exact h.1
    · exact h.2.1
  · apply stdSimplex.ext
    intro i
    fin_cases i
    · exact initialHornProductPairing_first_right_zero m n s
    · exact h.2.2.trans (initialHornProductPairing_first_right_zero m n s)

/-- 概要：積の pairing の型 I の次数は左因子の次元より一つ小さい値以上。
方針：左射影の全射性から有限集合の濃度を比較する。
規約：特に貼り付ける外側ホーンの次元は二以上。
使われ方：Kerodon §5.3.7（Tag 01US） の可逆な辺による外側ホーンの充填。 -/
lemma initialHornProductPairing_dim_ge (m n : ℕ)
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin (m + 2)) n) : m + 1 ≤ s.d := by
  have hs : Function.Surjective (fun i : Fin (s.d + 2) ↦ (s.x.cast s.hd).simplex.1 i) := by
    intro j
    by_cases hj : j = 0
    · subst j
      exact ⟨s.index.castSucc, (prodStdSimplex.pairingCore.isIndex_succ s.x s.hd s.index).1 s.isIndex |>.1⟩
    · exact prodStdSimplex.pairingCore.mem_range_left s.x s.hd j hj
  have hc := Fintype.card_le_of_surjective _ hs
  simp only [Fintype.card_fin] at hc
  omega

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
