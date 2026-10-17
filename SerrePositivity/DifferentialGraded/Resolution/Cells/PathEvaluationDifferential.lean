module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.EvaluationPrefix

/-! # 任意次数cell path評価の微分：先頭境界項と後方微分項

## 概要
任意次数cell path評価の微分：先頭境界項と後方微分項。

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
universe u v w z
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w}
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

lemma evaluationPrefix_boundary (i : I) (w : List I) (x y : D) :
    ((tensorLeftHom (homObject A D x (C.source i))
      (C.generator A D I i ⊗ C.term A D I w (C.target i) y)
      (C.generator A D I i ⊗ homObject A E (F.obj (C.target i)) (F.obj y))).f 0
      ((tensorLeftHom (C.generator A D I i) (C.term A D I w (C.target i) y)
        (homObject A E (F.obj (C.target i)) (F.obj y))).f 0
          (P.pathEvaluation w (C.target i) y))).comp
      (δ 0 1 (P.evaluationPrefixAction i x y)) (zero_add 1) =
    (C.replaceFirst A D I i w x y).comp (P.pathEvaluation w x y) (add_zero 1) := by
  have he :
      ((tensorLeftHom (homObject A D x (C.source i)) (C.term A D I w (C.source i) y)
        (homObject A E (F.obj (C.source i)) (F.obj y))).f 0
          (P.pathEvaluation w (C.source i) y)).comp
        (Cochain.ofHom (P.evaluationOriginalAction x (C.source i) y)) (zero_add 0) =
      (Cochain.ofHom (C.prependMap A D I w x (C.source i) y)).comp
        (P.pathEvaluation w x y) (zero_add 0) := by
    rw [evaluationOriginalAction, Cochain.ofHom_comp,
      ← Cochain.comp_assoc_of_third_is_zero_cochain,
      ← tensorZeroCochain_ofHom_left, ← pathEvaluation_prepend]
  rw [evaluationPrefixAction_differential,
    ← Cochain.comp_assoc_of_third_is_zero_cochain,
    ← tensorLeftHom_cochain_comp, boundaryAction_pathEvaluation,
    tensorLeftHom_cochain_comp, Cochain.comp_assoc_of_third_is_zero_cochain, he,
    ← Cochain.comp_assoc_of_second_is_zero_cochain, ← Family.replaceFirst_eq_head]

/-- 後方の任意次数cochainを、先頭Hom・生成元の評価作用へ合成する。 -/
def pathEvaluationTail (i : I) (w : List I) (x y : D) (p : ℤ)
    (f : Cochain (C.term A D I w (C.target i) y)
      (homObject A E (F.obj (C.target i)) (F.obj y)) p) :
    Cochain (C.term A D I (i :: w) x y) (homObject A E (F.obj x) (F.obj y)) p :=
  ((tensorLeftHom (homObject A D x (C.source i))
    (C.generator A D I i ⊗ C.term A D I w (C.target i) y)
    (C.generator A D I i ⊗ homObject A E (F.obj (C.target i)) (F.obj y))).f p
    ((tensorLeftHom (C.generator A D I i) (C.term A D I w (C.target i) y)
      (homObject A E (F.obj (C.target i)) (F.obj y))).f p f)).comp
    (P.evaluationPrefixAction i x y) (add_zero p)

lemma pathEvaluation_cons_differential (i : I) (w : List I) (x y : D) :
    δ 0 1 (P.pathEvaluation (i :: w) x y) =
    (C.replaceFirst A D I i w x y).comp (P.pathEvaluation w x y) (add_zero 1) +
    P.pathEvaluationTail i w x y 1 (δ 0 1 (P.pathEvaluation w (C.target i) y)) := by
  rw [pathEvaluation_cons_action,
    δ_comp _ _ (zero_add 0) 1 1 1 (zero_add 1) (zero_add 1) (zero_add 1),
    evaluationPrefix_boundary,
    homComplexMap_differential (tensorLeftHom _ _ _) 0 1,
    homComplexMap_differential (tensorLeftHom _ _ _) 0 1]
  simp only [Int.negOnePow_zero, one_smul]
  rfl

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
