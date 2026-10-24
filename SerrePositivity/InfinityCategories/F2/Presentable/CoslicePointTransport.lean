module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationCoslicePointFamily
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorUnitHom

/-!
概要：指定した全解の点から、元の底の coslice 全体への輸送を構成する。
方針：恒等点評価の標準切断の頂点を元の底上の全射へ戻す。
規約：恒等錐の像は指定された全空間の点と厳密に一致する。
使われ方：全解錐から作った Hom 比較の逆向きの射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
  (b : B _⦋0⦌) (w : vertexFiber p b _⦋0⦌)

/-- 概要：指定点から元の coslice 全体への、底を保つ輸送の全射。
方針：相対関手空間の標準切断の同じ頂点を通常の底上の射へ戻す。
規約：元の全射と底の一致条件を一緒に保持する。
使われ方：生成解の点を全対象上の解へ輸送する。 -/
def coslicePointTransport :
    {f : sliceUnder (SSet.yonedaEquiv.symm b) ⟶ E //
      f ≫ p = sliceUnderProjection (SSet.yonedaEquiv.symm b)} :=
  (relativeFunctorVertexEquiv p (sliceUnderProjection (SSet.yonedaEquiv.symm b))).symm
    ((leftFibrationCoslicePointSection p b).app (Opposite.op ⦋0⦌) w)

/-- 概要：選んだ全輸送の相対頂点は元の標準切断の頂点そのもの。
方針：相対関手の頂点の全単射の逆関係を使う。
規約：任意の同型な比較に選び直さない。
使われ方：同じ恒等点の厳密な回収。 -/
lemma coslicePointTransport_vertex :
    relativeFunctorVertex p (sliceUnderProjection (SSet.yonedaEquiv.symm b))
      (coslicePointTransport p b w).val (coslicePointTransport p b w).property =
        (leftFibrationCoslicePointSection p b).app (Opposite.op ⦋0⦌) w :=
  (relativeFunctorVertexEquiv p (sliceUnderProjection (SSet.yonedaEquiv.symm b))).apply_symm_apply _

/-- 概要：全輸送を元の恒等錐で評価すると指定した解の点を厳密に回収する。
方針：標準切断の評価式を全空間に含め、元の射の評価へ戻す。
規約：元の指定点 w.val を終値として保持する。
使われ方：coslice 上の二つの持ち上げを始対象で照合する条件。 -/
lemma coslicePointTransport_identity :
    (coslicePointTransport p b w).val.app (Opposite.op ⦋0⦌) (cosliceIdentityCone b) = w.val := by
  have h := congrArg (fun k ↦ k ≫ vertexFiberι p b)
    (leftFibrationCoslicePointSection_evaluate p b)
  dsimp only [leftFibrationCoslicePointEvaluate] at h
  rw [Category.assoc, Category.assoc,
    vertexFiberTransport_ι p (cosliceIdentityCone_projection b)] at h
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋0⦌)) w
  change (evaluateFunctorAt (cosliceIdentityCone b)).app (Opposite.op ⦋0⦌)
    (((leftFibrationCoslicePointSection p b).app (Opposite.op ⦋0⦌) w).val) = w.val at he
  rw [← coslicePointTransport_vertex p b w] at he
  change (evaluateFunctorAt (cosliceIdentityCone b)).app (Opposite.op ⦋0⦌)
    (functorVertex (coslicePointTransport p b w).val) = w.val at he
  rw [evaluateFunctorAt_functorVertex] at he
  exact he

end SerrePositivity.InfinityCategories.F2.Presentable
