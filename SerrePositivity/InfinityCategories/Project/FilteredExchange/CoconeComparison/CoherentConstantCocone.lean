module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingVertexEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningTransformationFamily
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoherentSmallConstantTarget
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.HomotopyCoconeRealization
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.CoherentTotalUnitRepresentation

/-!
概要：指定した全空間の射を表す coherent な余錐を構成する。
方針：定値標的比較で変換を回収し、両端固定で join 余錐へ実現する。
規約：指定射との比較同型を保持。使われ方：全空間射影からの余錐の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
  (a : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject z).obj)

/-- 概要：指定した全空間の射を表す変換と比較同型。
方針：定値標的比較の本質的全射性。
規約：指定射を変えない。使われ方：元の射影を表す余錐。 -/
def coherentConstantRepresentation : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentConstantRepresentation F z a :=
  Classical.choice <| by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coherentSmallConstantTargetMap_isQCatEquivalence F z
  obtain ⟨t, ⟨e⟩⟩ := h.choose.isEssentiallySurjective (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a))
  exact ⟨⟨t, e⟩⟩

/-- 概要：指定射を表す変換の実際の coherent 円柱。
方針：選択済み変換の辺を uncurry。
規約：両端は元の図式と定値図式。使われ方：join 実現への入力。 -/
def coherentConstantHomotopy : SSet.Homotopy F (SSet.const z) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (coherentConstantRepresentation F z a).1).toTruncated

/-- 概要：指定射の変換を元の両端を固定した余錐に実現。
方針：fat join 比較。規約：比較円柱も保持。使われ方：指定射との照合。 -/
def coherentConstantCoconeRealization :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.HomotopyCoconeRealization (coherentConstantHomotopy F z a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homotopyCoconeRealization (coherentConstantHomotopy F z a)

/-- 概要：元の全空間の指定射を表す native な余錐。
方針：比較付き実現の余錐を取る。
規約：元の図式の上の余錐。使われ方：全空間比較と余錐の接続。 -/
def coherentConstantCocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F :=
  (coherentConstantCoconeRealization F z a).cocone

/-- 概要：指定射を表す余錐の頂点は元の指定値。
方針：両端固定実現の頂点式。規約：厳密な等式。使われ方：標準余錐比較への入力。 -/
lemma coherentConstantCocone_vertex : (coherentConstantCocone F z a).vertex = z :=
  (coherentConstantCoconeRealization F z a).vertex_eq

end SerrePositivity.InfinityCategories.Project.FilteredExchange
