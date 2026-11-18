module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitDerived
public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitDerivedHomSource
public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitDerivedHomNormalization
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.RepresentedLocalization

/-!
# 元の E 代数極限の底と全複体図式の右導来極限の比較

概要：BM 命題 4.1・Hovey §5.4 の両計算対象を元の Hom 比較で同定する。
方針：同じ定値複体図式からの局所化 Hom の二つの自然同値を合成する。
規約：元の E 代数 frame の底も複体 frame の計算対象も保持する。
使われ方：一般 homotopy 極限の忘却後の導来比較。
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 2048
-- 二つの具体的な Hom 同値と普通の局所化の型を同時に照合するため。

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra Opposite
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：二つの計算対象への表現可能 Hom は元の複体上で自然に同型（Hovey §5.4）。
方針：同じ定値図式からの Hom の二つの同値と始域自然性を使う。
規約：元の複体の cofibrancy は不要。
使われ方：局所化圏上の対象の比較同型の復元。 -/
def carrierFramedLimitRestrictedHomIso (F : K ⥤ (operad A).Algebra) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let Q := (weakEquivalences (Complex A)).Q
    Q.op ⋙ yoneda.obj
        (Q.obj ((_root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K).obj ((Diagram.forget A K).obj F))) ≅
      Q.op ⋙ yoneda.obj (Q.obj ((framedLimitFunctor A K).obj F).carrier) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := CarrierDiagram.projectiveModelCategory A K
  let Q := (weakEquivalences (Complex A)).Q
  refine NatIso.ofComponents (fun Y =>
    ((_root_.SerrePositivity.ComplexLimits.framedLimitDerivedHomEquiv A K Y.unop ((Diagram.forget A K).obj F)).symm.trans
      (carrierFramedLimitDerivedHomEquiv A K Y.unop F)).toIso) ?_
  intro Y Z f
  ext x
  obtain ⟨z, rfl⟩ :=
    (_root_.SerrePositivity.ComplexLimits.framedLimitDerivedHomEquiv A K Y.unop ((Diagram.forget A K).obj F)).surjective x
  change carrierFramedLimitDerivedHomEquiv A K Z.unop F
      ((_root_.SerrePositivity.ComplexLimits.framedLimitDerivedHomEquiv A K Z.unop ((Diagram.forget A K).obj F)).symm
        (Q.map f.unop ≫ _root_.SerrePositivity.ComplexLimits.framedLimitDerivedHomEquiv A K Y.unop
          ((Diagram.forget A K).obj F) z)) =
    Q.map f.unop ≫ carrierFramedLimitDerivedHomEquiv A K Y.unop F
      ((_root_.SerrePositivity.ComplexLimits.framedLimitDerivedHomEquiv A K Y.unop ((Diagram.forget A K).obj F)).symm
        (_root_.SerrePositivity.ComplexLimits.framedLimitDerivedHomEquiv A K Y.unop ((Diagram.forget A K).obj F) z))
  rw [← _root_.SerrePositivity.ComplexLimits.framedLimitDerivedHomEquiv_source A K f.unop
    ((Diagram.forget A K).obj F) z, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact carrierFramedLimitDerivedHomEquiv_source A K f.unop F z

/-- 概要：元の計算対象の底は全複体図式の右導来極限の同じ値（BM 命題 4.1）。
方針：二つの自然な Hom 同値を反対局所化へ降ろして Yoneda で復元する。
規約：元の図式を忘却した複体図式で計算する。
使われ方：忘却後の一般右導来極限比較。 -/
def carrierFramedLimitComparisonIso (F : K ⥤ (operad A).Algebra) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let Q := (weakEquivalences (Complex A)).Q
    Q.obj ((_root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K).obj ((Diagram.forget A K).obj F)) ≅
      Q.obj ((framedLimitFunctor A K).obj F).carrier := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.comparisonIso
    (weakEquivalences (Complex A)).Q (weakEquivalences (Complex A))
    (carrierFramedLimitRestrictedHomIso A K F)

/-- 概要：底の比較同型の後合成は二つの元の Hom 同値の合成（Hovey §5.4）。
方針：局所化前の表現可能 Hom から復元する成分の計算を使う。
規約：元の複体の局所化像からの任意の射に対する式。
使われ方：通常錐の比較と終域図式の自然性の照合。 -/
lemma carrierFramedLimitComparisonIso_hom_apply (F : K ⥤ (operad A).Algebra)
    (Y : Complex A) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let := CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (Complex A)).Q
    ∀ x : Q.obj Y ⟶
      Q.obj ((_root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K).obj ((Diagram.forget A K).obj F)),
    x ≫ (carrierFramedLimitComparisonIso A K F).hom =
      carrierFramedLimitDerivedHomEquiv A K Y F
        ((_root_.SerrePositivity.ComplexLimits.framedLimitDerivedHomEquiv A K Y ((Diagram.forget A K).obj F)).symm x) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := CarrierDiagram.projectiveModelCategory A K
  dsimp only
  intro x
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.comparisonIso_hom_app
    (weakEquivalences (Complex A)).Q (weakEquivalences (Complex A))
    (carrierFramedLimitRestrictedHomIso A K F) Y x

/-- 概要：底の比較同型は元の通常錐の比較射を保持（BM 命題 4.1）。
方針：同じ通常錐の両 Hom 同値の正規化と比較同型の成分式を使う。
規約：任意の複体を頂点とする元の錐。
使われ方：右導来極限の比較が元の通常極限比較と両立すること。 -/
lemma carrierFramedLimitComparisonIso_cone (F : K ⥤ (operad A).Algebra)
    (c : Cone ((Diagram.forget A K).obj F)) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let Q := (weakEquivalences (Complex A)).Q
    Q.map (_root_.SerrePositivity.ComplexLimits.coneToFramedLimit A K ((Diagram.forget A K).obj F) c) ≫
        (carrierFramedLimitComparisonIso A K F).hom =
      Q.map (carrierConeToFramedLimit A K F c) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := CarrierDiagram.projectiveModelCategory A K
  let Q := (weakEquivalences (Complex A)).Q
  let QD := (weakEquivalences (K ⥤ Complex A)).Q
  let e := _root_.SerrePositivity.ComplexLimits.framedLimitDerivedHomEquiv A K c.pt ((Diagram.forget A K).obj F)
  have hc : e (QD.map c.π) =
      Q.map (_root_.SerrePositivity.ComplexLimits.coneToFramedLimit A K ((Diagram.forget A K).obj F) c) :=
    _root_.SerrePositivity.ComplexLimits.framedLimitDerivedHomEquiv_cone A K ((Diagram.forget A K).obj F) c
  have he : e.symm (Q.map
      (_root_.SerrePositivity.ComplexLimits.coneToFramedLimit A K ((Diagram.forget A K).obj F) c)) = QD.map c.π := by
    simpa only [Equiv.symm_apply_apply] using (congrArg e.symm hc).symm
  exact (carrierFramedLimitComparisonIso_hom_apply A K F c.pt _).trans
    ((congrArg (carrierFramedLimitDerivedHomEquiv A K c.pt F) he).trans
      (carrierFramedLimitDerivedHomEquiv_cone A K F c))

/-- 概要：底の比較同型は元の E 代数錐の比較射の忘却を保持（BM 命題 4.1）。
方針：底の通常錐の式と既存の代数比較の底との一致を合成する。
規約：元の coneToFramedLimit の同じ射を使う。
使われ方：元の通常極限比較の忘却後の導来比較。 -/
lemma carrierFramedLimitComparisonIso_forgetCone (F : K ⥤ (operad A).Algebra) (c : Cone F) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let Q := (weakEquivalences (Complex A)).Q
    Q.map (_root_.SerrePositivity.ComplexLimits.coneToFramedLimit A K ((Diagram.forget A K).obj F)
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)).mapCone c)) ≫
      (carrierFramedLimitComparisonIso A K F).hom = Q.map (coneToFramedLimit A K F c).hom := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact (carrierFramedLimitComparisonIso_cone A K F
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)).mapCone c)).trans
      (congrArg ((weakEquivalences (Complex A)).Q.map)
        (carrierConeToFramedLimit_forget A K F c))

end SerrePositivity.EInfinity.BarrattEccles
