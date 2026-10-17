module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathAction
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathEquations
public import SerrePositivity.DifferentialGraded.Complexes.TensorTwoUnitInsertion

/-! # 別端点を持つ一生成元pathの連結と単位因子の消去

## 概要
別端点を持つ一生成元pathの連結と単位因子の消去。

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
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

lemma generatorTerm_append (i : I) (w : List I) (y : D) :
    (C.generatorTerm A D I i ▷ C.term A D I w (C.target i) y) ≫
      C.appendMap A D I [i] w (C.source i) (C.target i) y =
    (λ_ (C.generator A D I i ⊗ C.term A D I w (C.target i) y)).inv ≫
      eId (Complex A) (C.source i) ▷ (C.generator A D I i ⊗ C.term A D I w (C.target i) y) := by
  simpa only [generatorTerm, appendMap, List.nil_append, term_nil] using
    tensorSandwich_append_distinct (C.generator A D I i)
      (homObject A D (C.source i) (C.source i)) (homObject A D (C.target i) (C.target i))
      (C.term A D I w (C.target i) y) (eId (Complex A) (C.source i)) (eId (Complex A) (C.target i))
      (C.prependMap A D I w (C.target i) (C.target i) y)
      (C.prependMap_left_unit A D I w (C.target i) y)

lemma prependMap_generatorTerm_append (i : I) (w : List I) (x y : D) :
    (homObject A D x (C.source i)) ◁
      ((C.generatorTerm A D I i ▷ C.term A D I w (C.target i) y) ≫
        C.appendMap A D I [i] w (C.source i) (C.target i) y) ≫
      C.prependMap A D I (i :: w) x (C.source i) y = 𝟙 (C.term A D I (i :: w) x y) := by
  rw [generatorTerm_append]
  simpa only [prependMap, term_cons, tensorHom_id] using
    tensorJoin_right_unit (homObject A D x (C.source i))
      (homObject A D (C.source i) (C.source i))
      (C.generator A D I i ⊗ C.term A D I w (C.target i) y)
      (eId (Complex A) (C.source i)) (eComp (Complex A) x (C.source i) (C.source i))
      (e_comp_id (Complex A) x (C.source i))

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
