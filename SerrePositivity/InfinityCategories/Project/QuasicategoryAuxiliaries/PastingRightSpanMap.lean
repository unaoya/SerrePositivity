module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PastingCorner

/-! # 右の三頂点部分の標準 span への符号化

概要：右の三頂点部分を標準 span ホーンへ単射で送る。
方針：(1,0)、(2,0)、(1,1) をそれぞれ 0、1、2 に符号化する。
規約：全長方形では単調な符号化を使い、部分図式上でホーンへの所属を確認する。
使われ方：S4 の右の部分図式と Λ[2,0] の同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：長方形の頂点を span の頂点番号へ符号化する単調写像。
方針：上段を二、下段の右端を一、残りを零へ送る。
規約：右の三頂点上では全単射。
使われ方：部分図式の標準単体での表示。 -/
def pastingSpanCode : Fin 3 × Fin 2 →o Fin 3 where
  toFun p := if p.2 = 0 then if p.1 = 2 then 1 else 0 else 2
  monotone' := by decide

/-- 概要：頂点の符号化を長方形の単体的な射へ延長する。
方針：各単体の二本の頂点列に単調な符号化を合成する。
規約：像はこの段階では標準二単体。
使われ方：右 span 上への制限。 -/
def pastingSpanCodeMap : ((Δ[2] : SSet.{u}) ⊗ Δ[1]) ⟶ Δ[2] where
  app n := ↾fun s ↦ stdSimplex.objEquiv.symm (SimplexCategory.mkHom
    (pastingSpanCode.comp ((stdSimplex.objEquiv s.1).toOrderHom.prod
      (stdSimplex.objEquiv s.2).toOrderHom)))
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro s
    apply stdSimplex.ext
    intro j
    rfl

/-- 概要：右の三頂点部分の単体の符号化は span ホーンに属する。
方針：最後の横座標が二なら縦座標は全て零、そうでなければ横座標は全て一である。
規約：退化単体を含む任意次数。
使われ方：符号化のホーンへの持ち上げ。 -/
lemma pastingRightSpan_code_mem_horn {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan : SSet.{u}) _⦋n⦌) :
    pastingSpanCodeMap.app (Opposite.op ⦋n⦌) s.val.val ∈ (horn 2 0).obj (Opposite.op ⦋n⦌) := by
  apply (mem_horn_iff_notMem_range _ 0).2
  by_cases hx : s.val.val.1 (Fin.last n) = 2
  · have hy : s.val.val.2 (Fin.last n) = 0 := by
      have h := s.val.property (Fin.last n) hx
      exact (by decide : ∀ y : Fin 2, y ≠ 1 → y = 0) _ h
    refine ⟨2, by decide, ?_⟩
    rintro ⟨j, hj⟩
    have hyj : s.val.val.2 j = 0 := by
      apply le_antisymm
      · calc
          s.val.val.2 j ≤ s.val.val.2 (Fin.last n) :=
            (stdSimplex.asOrderHom s.val.val.2).monotone (Fin.le_last j)
          _ = 0 := hy
      · exact Fin.zero_le _
    change (if s.val.val.2 j = 0 then if s.val.val.1 j = 2 then 1 else 0 else 2) = 2 at hj
    rw [ite_eq_left hyj] at hj
    split_ifs at hj <;> norm_num at hj
  · have hxlast : s.val.val.1 (Fin.last n) = 1 := by
      have hz := s.property (Fin.last n)
      exact (by decide : ∀ x : Fin 3, x ≠ 0 → x ≠ 2 → x = 1) _ hz hx
    refine ⟨1, by decide, ?_⟩
    rintro ⟨j, hj⟩
    have hxj : s.val.val.1 j = 1 := by
      have hlo := s.property j
      have hle := (stdSimplex.asOrderHom s.val.val.1).monotone (Fin.le_last j)
      change s.val.val.1 j ≤ s.val.val.1 (Fin.last n) at hle
      rw [hxlast] at hle
      exact (by decide : ∀ x : Fin 3, x ≠ 0 → x ≤ 1 → x = 1) _ hlo hle
    change (if s.val.val.2 j = 0 then if s.val.val.1 j = 2 then 1 else 0 else 2) = 1 at hj
    rw [hxj, ite_eq_right (by decide : (1 : Fin 3) ≠ 2)] at hj
    split_ifs at hj <;> norm_num at hj

/-- 概要：右の三頂点部分から標準 span ホーンへの符号化。
方針：長方形上の符号化を制限し、ホーンの所属条件で持ち上げる。
規約：余錐の頂点とは別の基底の図式の同型を作るための射。
使われ方：S4 の標準 span への移送。 -/
def pastingRightSpanToHorn : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan : SSet.{u}) ⟶ (horn 2 0 : SSet.{u}) :=
  Subcomplex.lift (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan.ι ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ pastingSpanCodeMap) (by
    intro n s hs
    obtain ⟨t, rfl⟩ := hs
    obtain ⟨⟨n⟩⟩ := n
    exact pastingRightSpan_code_mem_horn t)

private lemma code_injective (x x' : Fin 3) (y y' : Fin 2)
    (hx : x ≠ 0) (hx' : x' ≠ 0) (hc : x = 2 → y ≠ 1) (hc' : x' = 2 → y' ≠ 1)
    (h : pastingSpanCode (x, y) = pastingSpanCode (x', y')) : x = x' ∧ y = y' := by
  fin_cases x <;> fin_cases x' <;> fin_cases y <;> fin_cases y' <;>
    simp_all [pastingSpanCode]

/-- 概要：右の三頂点部分の符号化は単射。
方針：各単体の各頂点で符号化が単射であることを使う。
規約：全次数の単射性。
使われ方：逆の辺の貼り合わせから同型を得る。 -/
instance pastingRightSpanToHorn_mono : Mono pastingRightSpanToHorn.{u} := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro s t h
  have hcoord (j : Fin (n + 1)) : s.val.val.1 j = t.val.val.1 j ∧
      s.val.val.2 j = t.val.val.2 j := by
    have he := congrArg (fun z : (horn 2 0 : SSet.{u}) _⦋n⦌ ↦ z.val j) h
    exact code_injective _ _ _ _ (s.property j) (t.property j)
      (s.val.property j) (t.val.property j) he
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply stdSimplex.ext
    intro j
    exact (hcoord j).1
  · apply stdSimplex.ext
    intro j
    exact (hcoord j).2

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
