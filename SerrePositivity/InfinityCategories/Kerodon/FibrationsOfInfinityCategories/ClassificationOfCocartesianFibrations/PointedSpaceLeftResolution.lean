module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftFlagIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftResolution
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanOppositeCoefficients

/-!
概要：反転した空間値の pointed-space fiber と左 Hom の具体的な解像模型の同型。
方針：左 pinched Hom の旗の表示に、一点からの内部 Hom の標準同型を合成する。
規約：fiber の比較では同値から選んだ逆射を使わず、標準の厳密な同型を使う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な表現の fiber の具体的な比較射。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 概要：反転した Kan 複体の値上の普遍 fiber は元の Kan 複体の左 Hom の解像と厳密に同型。
方針：fiber を左 Hom にし、旗の同型と一点からの内部 Hom の同型を続ける。
規約：元の Kan 複体 K の値を反転した頂点における fiber。
使われ方：Kerodon Example 5.6.2.9（Tag 026S）、左右の係数を揃えた具体的な fiber 模型。 -/
noncomputable def pointedSpaceLeftResolutionIso (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj K)) ≅
      (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolution K.obj) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedSpaceFiberPinchedIso _ ≪≫
    eqToIso (congrArg₂ (fun x y ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj K))) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftPinchedFlagIso _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj K) ≪≫
    (SSet.uliftFunctor.{u + 1, u}).mapIso (SSet.opFunctor.mapIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointKanObjectHomIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj K))))

/-- 概要：元の Kan 複体から反転した値上の普遍 fiber への具体的な比較射。
方針：左 Hom の標準比較を持ち上げ、fiber の解像模型の標準同型の逆へ続ける。
規約：同値から選んだ逆射は使わない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、一般の coherent な表現の実際の fiber 比較。 -/
noncomputable def pointedSpaceLeftResolutionComparison (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj K.obj ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj K)) :=
  (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolutionComparison K.obj) ≫
    (pointedSpaceLeftResolutionIso K).inv

/-- 概要：具体的な fiber 比較を解像模型へ戻すと元の標準比較を回収する。
方針：標準同型の逆と順方向の往復を消す。
規約：構成した比較射そのものとの厳密な式。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、fiber 比較の自然性と同値性を解像へ移す。 -/
lemma pointedSpaceLeftResolutionComparison_factorization (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    pointedSpaceLeftResolutionComparison K ≫ (pointedSpaceLeftResolutionIso K).hom =
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolutionComparison K.obj) := by
  rw [pointedSpaceLeftResolutionComparison, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 概要：元の Kan 複体から反転した値上の普遍 fiber への具体的な比較射は同値。
方針：左 Hom の標準比較の同値を宇宙持ち上げし、標準同型を合成する。
規約：始域と終域はともに Kan 複体。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な表現の実際の比較の fiber の同値性。 -/
lemma pointedSpaceLeftResolutionComparison_isQCatEquivalence (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (pointedSpaceLeftResolutionComparison K) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolutionComparison_isQCatEquivalence K.obj).ulift_of_kan.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (pointedSpaceLeftResolutionIso K).symm).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
