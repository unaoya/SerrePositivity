module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FullyFaithful
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertexEquivalence
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningTransformationFamily
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoherentSmallConstantTarget
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTotalObject

/-!
概要：小さい全空間の Kan 置換への単位を、元の図式から定値図式への変換として表す。
方針：定値標的比較の本質的全射性で変換を選び、元の単位との同型を保持する。
規約：底は任意。余極限性はまだ主張しない。
使われ方：全空間模型を頂点とする native な余錐の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}

/-- 概要：全空間の単位を表す coherent な変換と、元の単位への比較同型。
方針：定値標的比較の像の頂点を元の単位の関手頂点と比較する。
規約：同値類だけでなく選択した変換と同型を保持。使われ方：余錐の普遍性の追跡。 -/
def CoherentConstantRepresentation
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (z : SpaceInfinity.{u} _⦋0⦌) (a : smallLeftUnstraightening F ⟶ (spaceInfinityObject z).obj) :=
  Σ t : (leftUnstraighteningTransformationSpace F (SSet.const z)) _⦋0⦌,
    VertexIso (X := (SSet.uliftFunctor.{u + 1, u}).obj
      ((ihom (smallLeftUnstraightening F)).obj (spaceInfinityObject z).obj))
      ((coherentSmallConstantTargetMap F z).app (Opposite.op ⦋0⦌) t)
      (ULift.up.{u + 1, u} (functorVertex a))

/-- 概要：全空間の実際の単位を表す変換を比較同型とともに選ぶ。
方針：定値標的比較の本質的全射性を単位の持ち上げた関手頂点へ適用する。
規約：後で使う単位との比較を捨てない。使われ方：指定頂点の native 余錐。 -/
def coherentTotalUnitRepresentation
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    CoherentConstantRepresentation F (coherentDiagramTotalVertex F)
      (coherentDiagramTotalUnit F) :=
  Classical.choice <| by
  have h := coherentSmallConstantTargetMap_isQCatEquivalence F (coherentDiagramTotalVertex F)
  obtain ⟨t, ⟨e⟩⟩ := h.choose.isEssentiallySurjective
    (ULift.up (functorVertex (coherentDiagramTotalUnit F)))
  exact ⟨⟨t, e⟩⟩

/-- 概要：選択した変換を、元の図式から全空間模型への実際の円柱に戻す。
方針：区間写像空間の頂点を関手空間の辺として読み、uncurry する。
規約：元の F と指定頂点に厳密に一致。使われ方：fat join の余錐。 -/
def coherentTotalUnitHomotopy
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    SSet.Homotopy F (SSet.const (coherentDiagramTotalVertex F)) :=
  simplicialHomotopyOfFunctorEdge
    (intervalMappingEdgeOfVertex (coherentTotalUnitRepresentation F).1).toTruncated

end SerrePositivity.InfinityCategories.F2
