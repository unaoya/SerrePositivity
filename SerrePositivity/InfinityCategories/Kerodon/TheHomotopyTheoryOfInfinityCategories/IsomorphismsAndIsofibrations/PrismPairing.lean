module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.CellExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.BoundaryPrism

/-!
概要：prism の正則 pairing の最初の辺の計算。
方針：右の射影が全頂点を通ることと、垂直な一歩の位置を使う。
規約：左の一次ホーンは時刻零の端点。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の外側ホーンを充填する辺。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：prism の pairing の型 I の単体の右の最初の値は零。
方針：右の射影の全射性で零を取る点を選び、単調性を使う。
規約：左側は二点鎖。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の先頭の fiber の同定。 -/
lemma prismPairing_first_right_zero (n : ℕ)
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin 1) n) :
    (s.x.cast s.hd).simplex.2 (0 : Fin (s.d + 2)) = 0 := by
  obtain ⟨i, hi⟩ := prodStdSimplex.pairingCore.mem_range_right s.x s.hd
    (0 : Fin (n + 1))
  apply le_antisymm _ (Fin.zero_le _)
  have h := stdSimplex.monotone_apply (s.x.cast s.hd).simplex.2 (Fin.zero_le i)
  exact h.trans (le_of_eq hi)

/-- 概要：欠ける面が零番目なら、prism の型 I の最初の二頂点は右で零を取る。
方針：pairing の垂直な一歩の定義と最初の値の計算を使う。
規約：型 I の単体の次数は s.d+1。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の先頭の垂直辺。 -/
lemma prismPairing_second_right_zero (n : ℕ)
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin 1) n) (hi : s.index = 0) :
    (s.x.cast s.hd).simplex.2 (1 : Fin (s.d + 2)) = 0 := by
  have h := (prodStdSimplex.pairingCore.isIndex_succ s.x s.hd s.index).1 s.isIndex
  have hr := h.2.2
  rw [hi] at hr
  exact hr.trans (prismPairing_first_right_zero n s)

/-- 概要：prism の最初の頂点上の垂直辺。
方針：第一成分を標準辺、第二成分を最初の頂点の定値辺とする。
規約：時刻零から時刻一へ向かう。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の fiber 内の可逆辺。 -/
def prismFirstVerticalEdge (n : ℕ) : ((Δ[1] : SSet.{u}) ⊗ Δ[n]) _⦋1⦌ :=
  ⟨SSet.yonedaEquiv (𝟙 Δ[1]), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) 1⟩

/-- 概要：零番目の面で対になる prism の単体の最初の辺は固定した垂直辺。
方針：pairing の垂直な一歩の条件を二つの頂点で計算する。
規約：標準辺は最初の二頂点を選ぶ。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の特別な外側ホーン。 -/
lemma prismPairing_firstEdge_eq (n : ℕ)
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin 1) n) (hi : s.index = 0) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[n]).map
      (stdSimplex.objEquiv (stdSimplex.edge.{u} (s.d + 1) 0 1 (Fin.zero_le _))).op
        (s.x.cast s.hd).simplex = prismFirstVerticalEdge n := by
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
    · exact prismPairing_first_right_zero n s
    · exact prismPairing_second_right_zero n s hi

/-- 概要：正次元の prism の最初の垂直辺は境界の prism に含まれる。
方針：第二成分の定値辺は最後の頂点を値に取らない。
規約：標準単体の次元は n+1。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の元の部分複体での辺の固定。 -/
lemma prismFirstVerticalEdge_mem (n : ℕ) :
    prismFirstVerticalEdge.{u} (n + 1) ∈
      (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).obj (Opposite.op ⦋1⦌) := by
  rw [Subcomplex.mem_unionProd_iff]
  left
  apply (mem_boundary_iff_notMem_range _).2
  refine ⟨Fin.last (n + 1), ?_⟩
  rintro ⟨i, hi⟩
  have he : (0 : Fin (n + 2)) = Fin.last (n + 1) := hi
  have h := congrArg Fin.val he
  simp only [Fin.val_zero, Fin.val_last] at h
  omega

/-- 概要：最初の垂直辺は収縮の下で最初の頂点に定値。
方針：二つの時刻で右側の値がどちらも零であることを使う。
規約：全次元で成立する。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の fiber に属することの確認。 -/
lemma prismFirstVerticalEdge_contraction (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstContraction.{u} n).app (Opposite.op ⦋1⦌) (prismFirstVerticalEdge n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) 1 := by
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 概要：prism の pairing の型 II の次数は右側の標準単体の次元以上。
方針：右の射影が全射なので頂点数を比較する。
規約：s.d は型 I の一つ低い次数。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の外側ホーンが二次元以上であること。 -/
lemma prismPairing_dim_ge (n : ℕ)
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin 1) n) : n ≤ s.d := by
  have hs : Function.Surjective (fun i : Fin (s.d + 1) ↦ s.δ.simplex.2 i) := by
    intro j
    exact prodStdSimplex.pairingCore.mem_range_right s.δ rfl j
  have hc := Fintype.card_le_of_surjective _ hs
  simp only [Fintype.card_fin] at hc
  omega

/-- 概要：prism の pairing の型 II の次数は右側の標準単体の次元に等しい。
方針：射影の全射性による下界と、標準単体の積の次元による上界を合わせる。
規約：全ての貼り付けるセルは同じ次元 n+1 を持つ。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の有限 prism 分解。 -/
lemma prismPairing_dim_eq (n : ℕ)
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin 1) n) : s.d = n := by
  have hl := prismPairing_dim_ge n s
  have hu := SSet.dim_lt_of_nonDegenerate ((Δ[1] : SSet.{u}) ⊗ Δ[n])
    ⟨(s.x.cast s.hd).simplex, (s.x.cast s.hd).nonDegenerate⟩ (1 + n + 1)
  change s.d + 1 < 1 + n + 1 at hu
  omega

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
