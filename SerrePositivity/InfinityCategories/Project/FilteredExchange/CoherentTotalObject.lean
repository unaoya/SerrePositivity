module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaces
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentFilteredTotalDetection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanWeakEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.WeakHomotopyPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy

/-!
概要：coherent 図式の小さい全空間の Kan 模型と、その実際の頂点・単位を整える。
方針：Kan 対象と頂点の厳密な往復を使い、単位の標的を頂点の値で表示する。
規約：底の filtered 性は不要。使われ方：全空間模型を頂点とする coherent な余錐。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {B : SSet.{u}}

/-- 概要：全空間の Kan 模型を元の宇宙の Kan 対象に束ねる。
方針：具体的な Kan 置換の充填性を添える。
規約：底の filtered 性は不要。使われ方：実際の 𝒮 の頂点。 -/
def coherentDiagramTotalKanObject
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F, inferInstance⟩

/-- 概要：全空間の Kan 模型が定める 𝒮 の頂点。
方針：既存の Kan 対象の頂点表示を使う。
規約：元の宇宙 u の対象。使われ方：coherent な余錐の指定頂点。 -/
def coherentDiagramTotalVertex
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (coherentDiagramTotalKanObject F)

/-- 概要：全空間の指定頂点から取り出す値は元の Kan 模型そのもの。
方針：Kan 対象と 𝒮 の頂点の厳密な往復の対象成分を取る。
規約：比較同値ではなく等式。使われ方：単位の型の正規化。 -/
lemma coherentDiagramTotalVertex_object
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (coherentDiagramTotalVertex F)).obj = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F :=
  congrArg (fun K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} ↦ K.obj)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertexEquiv.left_inv (coherentDiagramTotalKanObject F))

/-- 概要：実際の単位の標的を指定した 𝒮 の頂点の値で表示する。
方針：構成済みの単位に厳密な頂点の往復の等式を合成する。
規約：台の射は元の Kan 置換の単位。使われ方：定値標的比較による変換の回収。 -/
def coherentDiagramTotalUnit
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (coherentDiagramTotalVertex F)).obj :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F) ≫
    eqToHom (coherentDiagramTotalVertex_object F).symm

/-- 概要：頂点表示の単位を元の Kan 模型へ戻すと実際の置換の単位になる。
方針：頂点の往復の二つの等式の射を消去する。
規約：射の厳密な等式。使われ方：余錐の比較を元の単位で検証する。 -/
lemma coherentDiagramTotalUnit_factor
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    coherentDiagramTotalUnit F ≫ eqToHom (coherentDiagramTotalVertex_object F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F) := by
  simp only [coherentDiagramTotalUnit, eqToHom_refl, Category.comp_id]

/-- 概要：指定頂点の値への実際の単位は弱ホモトピー同値。
方針：元の置換の単位の弱同値性から、頂点の往復の同型を消去する。
規約：元の全空間の Kan 性は不要。使われ方：余錐の普遍性の写像空間による検証。 -/
lemma coherentDiagramTotalUnit_isWeakHomotopyEquivalence
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (coherentDiagramTotalUnit F) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (eqToIso (coherentDiagramTotalVertex_object F))).isWeakHomotopyEquivalence
  apply h.cancel_right
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    (coherentDiagramTotalUnit F ≫ eqToHom (coherentDiagramTotalVertex_object F))
  rw [coherentDiagramTotalUnit_factor]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacementUnit_isWeakHomotopyEquivalence _

/-- 概要：全空間の単位による任意の Kan 標的への前合成は実際のホモトピー同値。
方針：弱同値の Kan 標的への前合成の判定を使う。
規約：任意のパラメータを持つ写像空間の比較。使われ方：余錐の全 Hom の判定。 -/
lemma coherentDiagramTotalUnit_pre_homotopyEquivalence
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (Z : SSet.{u}) [KanComplex Z] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((pre (coherentDiagramTotalUnit F)).app Z) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.pre_isSimplicialHomotopyEquivalence_of_weakHomotopyEquivalence _
    (coherentDiagramTotalUnit_isWeakHomotopyEquivalence F) Z

end SerrePositivity.InfinityCategories.Project.FilteredExchange
