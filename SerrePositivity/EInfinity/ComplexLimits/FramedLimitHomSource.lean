module

public import SerrePositivity.EInfinity.ComplexLimits.FramedLimitHomPiZero
public import SerrePositivity.EInfinity.ComplexLimits.FramedLimitProbeLocalization
public import SerrePositivity.EInfinity.ComplexLimits.FramedLimitConeSource
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.TensorPiZeroTarget

/-!
# 具体的な計算対象への導来 Hom の始域自然性

概要：BM 命題 4.1・Hovey §5.4 の右錐の π₀ 比較は元の始域の射に自然。
方針：反対圏の重み付き錐の終域自然性と試験始域の局所化同型を合成する。
規約：前合成は元の複体射の同じ局所化像。
使われ方：定値図式との導来随伴の Hom 比較の始域自然性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.ComplexLimits

open CategoryTheory Limits _root_.HomotopicalAlgebra Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：実際の計算対象への Hom の π₀ 比較は始域に自然（Hovey §5.4）。
方針：同じ試験始域の前合成の式を反対化し、比較同型の逆の自然性を使う。
規約：元の複体に cofibrancy は要求しない。
使われ方：導来 Hom 同値の計算対象側の始域自然性。 -/
lemma framedLimitHomPiZeroEquiv_source {Y Z : (Complex A)} (f : Y ⟶ Z)
    (F : K ⥤ (Complex A)) (z : SSet.π₀ ((framedLimitConeSpace A K Z).obj F)) :
    let := projectiveModelCategory A
    let Q := (weakEquivalences (Complex A)).Q
    framedLimitHomPiZeroEquiv A K Y F
        (SSet.mapπ₀ ((framedLimitConeSourceMap A K f).app F) z) =
      Q.map f ≫ framedLimitHomPiZeroEquiv A K Z F z := by
  let := projectiveModelCategory A
  let Q := (weakEquivalences (Complex A)).Q
  have : Q.op.IsLocalization (weakEquivalences (Complex A)ᵒᵖ) := by
    rw [weakEquivalences_op]
    infer_instance
  let P := framedLimitProbeFunctor A
  have hp (X : (Complex A)) : IsCofibrant (P.obj X) := framedLimitProbe_cofibrant A X
  have hpf (X : (Complex A)) : IsFibrant (op (P.obj X)) :=
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fibrantOp_of_cofibrant _
  let e (X : (Complex A)) :=
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv Kᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
      (rightFrameDiagram A K F) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K)
      (fun k => rightFrame_cofibrant A (F.obj k.unop))
      (fun k _ _ g => rightFrame_homotopicallyConstant A (F.obj k.unop) g) Q.op (op (P.obj X))
  have hn : e Y (SSet.mapπ₀ ((framedLimitConeSourceMap A K f).app F) z) =
      e Z z ≫ Q.op.map (P.map f).op :=
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv_target Kᵒᵖ
      (C := (Complex A)ᵒᵖ) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) (rightFrameDiagram A K F)
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K) (fun k => rightFrame_cofibrant A (F.obj k.unop))
      (fun k _ _ g => rightFrame_homotopicallyConstant A (F.obj k.unop) g) Q.op (P.map f).op z
  have hu : (e Y (SSet.mapπ₀ ((framedLimitConeSourceMap A K f).app F) z)).unop =
      Q.map (P.map f) ≫ (e Z z).unop := by
    simpa only [unop_comp, Functor.op_map, Quiver.Hom.unop_op] using
      congrArg (fun h : Q.op.obj ((FrameWeightRealization.functor Kᵒᵖ
          (rightFrameDiagram A K F)).obj (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)) ⟶ Q.op.obj (op (P.obj Y)) =>
        h.unop) hn
  let p := framedLimitProbeLocalizedIso A
  have hpn : Q.map f ≫ (p.app Z).inv = (p.app Y).inv ≫ Q.map (P.map f) :=
    p.inv.naturality f
  change (p.app Y).inv ≫
      (e Y (SSet.mapπ₀ ((framedLimitConeSourceMap A K f).app F) z)).unop ≫ 𝟙 _ =
    Q.map f ≫ ((p.app Z).inv ≫ (e Z z).unop ≫ 𝟙 _)
  refine (congrArg (fun h : Q.obj (P.obj Y) ⟶ Q.obj ((framedLimitFunctor A K).obj F) =>
    (p.app Y).inv ≫ h ≫ 𝟙 _) hu).trans ?_
  simp only [Category.comp_id, ← Category.assoc]
  exact congrArg (fun h => h ≫ (e Z z).unop) hpn.symm

end SerrePositivity.EInfinity.ComplexLimits
