module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedSpaceLeftResolution
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseOppositeKanComparison

/-!
概要：一般の coherent な図式の反転した共通モデルの unstraightening の fiber を左解像で表示する。
方針：共通解像上の値を取り出し、反転した値の普遍 fiber の厳密な模型を適用する。
規約：各 fiber の具体的な比較であり、図式全体の復元の自然性は別に証明する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、一般の coherent な図式の復元比較の fiber での座標。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 概要：一般の図式を共通解像へ移したときの頂点の Kan 複体。
方針：持ち上げた図式の coherent な頂点から元の対象を取り出す。
規約：元の F の値との比較は関手同型を介する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、左解像の具体的な入力となる共通モデルの値。 -/
noncomputable def edgewiseCoherentDiagramValue {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (b : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.edgewiseCoherentDiagramLift F).app (Opposite.op ⦋0⦌) b)).val

/-- 概要：反転した共通モデルの頂点の値は、共通解像で取り出した Kan 複体の反転。
方針：coherent な頂点の復元則と豊穣関手の頂点での公式を使う。
規約：ここでは元の F の値との厳密な等式を主張しない。
使われ方：Kerodon Example 5.6.2.9（Tag 026S）、普遍 fiber の左解像の同型の適用条件。 -/
lemma edgewiseCoherentOppositeReplacement_vertex {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseCoherentOppositeReplacement F).app (Opposite.op ⦋0⦌) b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj (edgewiseCoherentDiagramValue F b)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOppositeKanEnriched).app (Opposite.op ⦋0⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.edgewiseCoherentDiagramLift F).app (Opposite.op ⦋0⦌) b) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.edgewiseCoherentDiagramLift F).app (Opposite.op ⦋0⦌) b),
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent]
  rfl

/-- 概要：反転した共通モデルの unstraightening の各 fiber は共通解像の値の左解像と厳密に同型。
方針：引き戻しの fiber を普遍 fiber へ移し、値の公式と左解像の標準同型を続ける。
規約：底 B の quasicategory 性を仮定しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、一般の coherent な図式の fiber の具体的な表示。 -/
noncomputable def edgewiseOppositeUnstraighteningFiberResolutionIso {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseCoherentOppositeReplacement F)) b ≅
      (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolution (edgewiseCoherentDiagramValue F b).obj) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningFiberIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseCoherentOppositeReplacement F) b ≪≫
    eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection) (edgewiseCoherentOppositeReplacement_vertex F b)) ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftResolutionIso (edgewiseCoherentDiagramValue F b)

/-- 概要：共通解像の値から一般の coherent な図式の反転モデルの fiber への具体的な比較射。
方針：値の左解像への標準比較を持ち上げ、fiber の厳密な座標同型の逆を続ける。
規約：同値の逆の選択は使わない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、復元比較の各 fiber への入力となる実際の射。 -/
noncomputable def edgewiseOppositeUnstraighteningFiberComparison {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj (edgewiseCoherentDiagramValue F b).obj ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseCoherentOppositeReplacement F)) b :=
  (SSet.uliftFunctor.{u + 1, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolutionComparison (edgewiseCoherentDiagramValue F b).obj) ≫
    (edgewiseOppositeUnstraighteningFiberResolutionIso F b).inv

/-- 概要：共通解像の値から反転モデルの実際の fiber への比較射は同値。
方針：左解像の標準比較の同値を持ち上げ、厳密な fiber の座標同型を合成する。
規約：各 fiber の射そのものの同値性。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、一般の coherent な図式の復元比較の fiber での検査。 -/
lemma edgewiseOppositeUnstraighteningFiberComparison_isQCatEquivalence {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (edgewiseOppositeUnstraighteningFiberComparison F b) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolutionComparison_isQCatEquivalence
    (edgewiseCoherentDiagramValue F b).obj).ulift_of_kan.comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (edgewiseOppositeUnstraighteningFiberResolutionIso F b).symm).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
