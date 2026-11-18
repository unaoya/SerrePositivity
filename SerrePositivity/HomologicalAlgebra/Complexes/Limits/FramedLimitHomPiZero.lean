module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitConePiZero
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.TensorPiZero
public import Mathlib.CategoryTheory.Localization.Opposite

/-!
# 右 frame の錐と具体的な極限計算対象への導来 Hom

概要：BM 命題 4.1・Hovey §5.4 の同じ重み付き end への局所化 Hom を計算する。
方針：反対圏の重み付き実現の π₀ 比較を元の圏へ戻し、試験始域の置換を消す。
規約：元の計算対象を別の導来極限候補へ置き換えない。
使われ方：定値図式との導来随伴の Hom の同値。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.ComplexLimits

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra _root_.Opposite
open _root_.SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：右 frame の錐の π₀ は実際の計算対象への局所化 Hom（Hovey §5.4）。
方針：反対圏の実現の Hom 比較と射の unop、試験始域の比較を合成する。
規約：元の Y と計算した framedLimitFunctor の値を使う。
使われ方：計算関手の導来随伴の Hom 同値の片側。 -/
def framedLimitHomPiZeroEquiv (Y : (Complex A)) (F : K ⥤ (Complex A)) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let Q := (weakEquivalences (Complex A)).Q
    SSet.π₀ ((_root_.SerrePositivity.ComplexLimits.framedLimitConeSpace A K Y).obj F) ≃
      (Q.obj Y ⟶ Q.obj ((_root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K).obj F)) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let Q := (weakEquivalences (Complex A)).Q
  have : Q.op.IsLocalization (weakEquivalences (Complex A)ᵒᵖ) := by
    rw [weakEquivalences_op]
    infer_instance
  have := _root_.SerrePositivity.ComplexLimits.framedLimitProbe_cofibrant A Y
  have : IsFibrant (op (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A Y)) :=
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fibrantOp_of_cofibrant _
  let e := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv Kᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
    (_root_.SerrePositivity.ComplexLimits.rightFrameDiagram A K F) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K)
    (fun k => _root_.SerrePositivity.ComplexLimits.rightFrame_cofibrant A (F.obj k.unop))
    (fun k _ _ f => _root_.SerrePositivity.ComplexLimits.rightFrame_homotopicallyConstant A (F.obj k.unop) f) Q.op
    (op (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A Y))
  have : IsIso (Q.map (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A Y)) :=
    Localization.inverts Q (weakEquivalences (Complex A)) _
      (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison_quasiIso A Y)
  exact e.trans ((show
      (Q.op.obj ((FrameWeightRealization.functor Kᵒᵖ (_root_.SerrePositivity.ComplexLimits.rightFrameDiagram A K F)).obj
        (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)) ⟶ Q.op.obj (op (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A Y))) ≃
      (Q.obj (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A Y) ⟶ Q.obj ((_root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K).obj F)) from
    { toFun := fun f => f.unop
      invFun := fun f => f.op
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans
    (Iso.homCongr (asIso (Q.map (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A Y))) (Iso.refl _)))

/-- 概要：元の定値図式と具体的な計算対象の導来 Hom の同値（Hovey §5.4）。
方針：右 frame の同じ錐の π₀ を介した二つの同値を合成する。
規約：ここでは対象ごとの同値を構成し、導来随伴の自然性は別に確認する。
使われ方：一般 homotopy 極限の右導来普遍性の Hom 計算。 -/
def framedLimitDerivedHomEquiv (Y : (Complex A)) (F : K ⥤ (Complex A)) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (Complex A)).Q
    let QD := (weakEquivalences (K ⥤ (Complex A))).Q
    (QD.obj ((Functor.const K).obj Y) ⟶ QD.obj F) ≃
      (Q.obj Y ⟶ Q.obj ((_root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K).obj F)) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  exact (_root_.SerrePositivity.ComplexLimits.framedLimitConePiZeroEquiv A K Y F).symm.trans (_root_.SerrePositivity.ComplexLimits.framedLimitHomPiZeroEquiv A K Y F)

end SerrePositivity.ComplexLimits
