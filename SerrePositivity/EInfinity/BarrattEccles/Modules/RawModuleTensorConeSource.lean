module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeFamily
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementSourceRoof
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses

/-!
# 元の全 cone 族の同じ加群導来源への像

概要：M10 の同じ全区間族を同じ選択済み moduleResolution で送る。
方針：全通常図式の合成式と元の指定頂点を等式で移送する。
規約：HA §1.3.4、同じ実ホモトピー写像を保持する。
使われ方：同じ全 augmentation・実評価屋根と元の K の射の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SSet
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.SimplicialModel
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma coneHomotopyTransport_h {K T : SSet.{u + 1}} {f g f' g' : K ⟶ T}
    (hf : f = f') (hg : g = g') (H : SSet.Homotopy f g) :
    ((congrArg₂ (fun a b => SSet.Homotopy a b) hf hg).mp H).h = H.h := by
  cases hf
  cases hg
  rfl

/-- 概要：同じ全区間族を任意の関手で後合成する。
方針：元の全ホモトピーを送り、同じ定値端点の自然性で移送する。
規約：HA §1.3.4、同じ全族。使われ方：元の解像度への代入。 -/
def strictRawModuleTensorConeMappedHomotopy {C : SSet.{u + 1}}
    (F : dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) ⟶ C) :
    SSet.Homotopy
      (SSet.const (F.app (op ⦋0⦌)
        ((dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm
          (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)))))
      (strictRawModuleTensorElementNerveDiagram A X P Q ≫ F) :=
  (congrArg₂ (fun a b => SSet.Homotopy a b)
    (SSet.const_comp _ F) rfl).mp
      (HomotopyClasses.postHomotopy F (strictRawModuleTensorConeHomotopy A X P Q))

/-- 概要：同じ後合成族の実写像は元の同じ全写像の後合成。
方針：端点の等式移送は同じホモトピー写像を保つ。
規約：HA §1.3.4、元の全単体。使われ方：同じ全三角形の比較。 -/
lemma strictRawModuleTensorConeMappedHomotopy_h {C : SSet.{u + 1}}
    (F : dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) ⟶ C) :
    (strictRawModuleTensorConeMappedHomotopy A X P Q F).h =
      (strictRawModuleTensorConeHomotopy A X P Q).h ≫ F :=
  coneHomotopyTransport_h
    (SSet.const_comp
      ((dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm
        (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))) F)
    rfl (HomotopyClasses.postHomotopy F (strictRawModuleTensorConeHomotopy A X P Q))

/-- 概要：同じ全通常図式の同じ解像度像は元の導来源の全図式。
方針：元の同じ ULiftHom 表示と同じ源の合成を結合し直す。
規約：HA §1.3.4、全関手の等式。使われ方：元の屋根の全始域。 -/
lemma strictRawModuleTensorElementNerveDiagram_source :
    strictRawModuleTensorElementNerveDiagram A X P Q ≫
      moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X)) =
    strictRawModuleDiagramSource A X (strictRawModuleTensorElementDiagram A X P Q) :=
  Category.assoc _ _ _

/-- 概要：同じ解像度で送った元の先端は同じ通常源の指定頂点。
方針：元の同じ源の頂点式を使う。
規約：HA §1.3.4、指定頂点。使われ方：元の屋根の同じ定値端点。 -/
lemma strictRawModuleTensorConeSource_vertex :
    (moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X))).app (op ⦋0⦌)
      ((dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm
        (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))) =
    (strictRawModuleSource A X).app (op ⦋0⦌)
      (nerveVertex ((ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)).obj
        ((strictRawModuleProbeFunctor A X).obj P))) :=
  (strictRawModuleSource_vertex A X _).symm

/-- 概要：同じ全 cone の元の指定導来源による全区間像。
方針：同じ全後合成を元の全図式と指定頂点の等式で移送する。
規約：HA §1.3.4、同じ解像度。使われ方：全評価屋根との同じ比較。 -/
def strictRawModuleTensorConeSourceHomotopy :
    SSet.Homotopy
      (SSet.const ((strictRawModuleSource A X).app (op ⦋0⦌)
        (nerveVertex ((ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)).obj
          ((strictRawModuleProbeFunctor A X).obj P)))))
      (strictRawModuleDiagramSource A X (strictRawModuleTensorElementDiagram A X P Q)) :=
  (congrArg₂ (fun a b => SSet.Homotopy a b)
    (congrArg (fun z => SSet.const (X := nerve (strictRawModuleTensorElementIndex A X P Q)) z)
      (strictRawModuleTensorConeSource_vertex A X P))
    (strictRawModuleTensorElementNerveDiagram_source A X P Q)).mp
      (strictRawModuleTensorConeMappedHomotopy A X P Q
        (moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X))))

/-- 概要：同じ指定源への移送後も元の同じ全ホモトピー写像を保つ。
方針：両端の等式移送と同じ後合成の式を合成する。
規約：HA §1.3.4、元の全写像。使われ方：同じ augmentation 三角形。 -/
lemma strictRawModuleTensorConeSourceHomotopy_h :
    (strictRawModuleTensorConeSourceHomotopy A X P Q).h =
      (strictRawModuleTensorConeHomotopy A X P Q).h ≫
        moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X)) := by
  exact (coneHomotopyTransport_h
    (congrArg (fun z => SSet.const (X := nerve (strictRawModuleTensorElementIndex A X P Q)) z)
      (strictRawModuleTensorConeSource_vertex A X P))
    (strictRawModuleTensorElementNerveDiagram_source A X P Q)
    (strictRawModuleTensorConeMappedHomotopy A X P Q
      (moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X))))).trans
    (strictRawModuleTensorConeMappedHomotopy_h A X P Q _)

/-- 概要：同じ元の導来源の全区間族を全関手圏の射として保持する。
方針：同じ全ホモトピーの辺の類を取る。
規約：HA §1.3.4、同じ全パラメータ。使われ方：元の全屋根との比較。 -/
def strictRawModuleTensorConeSourceFamilyHom :
    FunctorHom
      (SSet.const ((strictRawModuleSource A X).app (op ⦋0⦌)
        (nerveVertex ((ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)).obj
          ((strictRawModuleProbeFunctor A X).obj P)))))
      (strictRawModuleDiagramSource A X (strictRawModuleTensorElementDiagram A X P Q)) :=
  Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy (strictRawModuleTensorConeSourceHomotopy A X P Q))

end SerrePositivity.EInfinity.BarrattEccles
