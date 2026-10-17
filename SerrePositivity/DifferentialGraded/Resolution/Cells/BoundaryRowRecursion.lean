module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Prefix
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryNaturality
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryOperator
public import SerrePositivity.DifferentialGraded.Complexes.TensorClosedZero

/-! # 任意次数cell pathの境界置換：BoundaryRowRecursion

## 概要
任意次数cell pathの境界置換：BoundaryRowRecursion。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

/-- 後方cochainを先頭Homと生成元でtensorし、先頭を追加したpath直和へ送る。 -/
def prefixTailCochain (b : I) (w : List I) (x y : D) (p : ℤ)
    (f : Cochain (C.term A D I w (C.target b) y) (C.internalHom A D I (C.target b) y) p) :
    Cochain (C.term A D I (b :: w) x y) (C.internalHom A D I x y) p :=
  ((tensorLeftHom (homObject A D x (C.source b)) (C.generator A D I b ⊗ C.term A D I w (C.target b)
    y)
    (C.generator A D I b ⊗ C.internalHom A D I (C.target b) y)).f p
    ((tensorLeftHom (C.generator A D I b) (C.term A D I w (C.target b) y)
      (C.internalHom A D I (C.target b) y)).f p f)).comp
    (Cochain.ofHom (C.prefixPath A D I b x y)) (add_zero p)

/-- 後方の消去項は短いpathの消去項を二重tensorし、先頭を追加したもの。 -/
lemma replaceSummand_cons_succ (b : I) (w : List I) (i : ℕ) (x y : D) :
    C.replaceSummand A D I (b :: w) (i + 1) x y =
    C.prefixTailCochain A D I b w x y 1 (C.replaceSummand A D I w i (C.target b) y) := by
  rw [prefixTailCochain, replaceSummand, replaceSummand, replaceFace_succ,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, prefixPath_inclusion]
  rfl

/-- 非空pathの消去和は、先頭生成元の消去と、先頭を保持する後方消去和の和である。 -/
lemma replaceRow_cons (b : I) (w : List I) (x y : D) :
    C.replaceRow A D I (b :: w) x y =
    (C.replaceFirst A D I b w x y).comp (Cochain.ofHom (C.inclusion A D I w x y)) (add_zero 1) +
    C.prefixTailCochain A D I b w x y 1 (C.replaceRow A D I w (C.target b) y) := by
  let R : Cochain (C.term A D I w (C.target b) y) (C.internalHom A D I (C.target b) y) 1 →+
      Cochain (C.term A D I (b :: w) x y) (C.internalHom A D I x y) 1 :=
    { toFun := C.prefixTailCochain A D I b w x y 1
      map_zero' := by simp only [prefixTailCochain, map_zero, Cochain.zero_comp]
      map_add' := fun f g => by
        simp only [prefixTailCochain, map_add]
        exact Cochain.add_comp _ _ _ (add_zero 1) }
  have hs : ∑ i ∈ Finset.range w.length, C.replaceSummand A D I (b :: w) (i + 1) x y =
      R (C.replaceRow A D I w (C.target b) y) := by
    rw [replaceRow, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact C.replaceSummand_cons_succ A D I b w i x y
  have hz : C.replaceSummand A D I (b :: w) 0 x y =
      (C.replaceFirst A D I b w x y).comp (Cochain.ofHom (C.inclusion A D I w x y)) (add_zero 1) :=
        rfl
  rw [replaceRow, List.length_cons, Finset.sum_range_succ', hs, hz]
  exact add_comm _ _

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
