module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FullyFaithful
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.MappingSpaceLeft
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeTransformationPoint
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoherentCoconeTotalComparison
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTotalCocone
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTotalColimit
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTotalMap
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTotalMapCocone
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.CoherentTotalObject
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconePointHomFamily
public import SerrePositivity.InfinityCategories.Stable.CoconeMappingSpace

/-!
概要：全空間の射が表す指定余錐を native な余極限頂点からの射で表示する。
方針：元の全 Hom による余錐族の同値を使い、指定余錐との比較同型を保持する。
規約：比較同型を捨てない。使われ方：具体的な Kan 射と native 余極限写像の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})
  (a : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G)

/-- 概要：指定余錐を表す native な射と、元の余錐への比較同型のデータ。
方針：全 Hom の族の像と指定余錐を比較。
規約：元の余極限余錐を固定。使われ方：写像の標準比較への移送。 -/
def CoherentTotalMapNativeRepresentation :=
  Σ x : (pinchedHomLeft (coherentDiagramTotalCocone F).vertex
      (coherentDiagramTotalVertex G)) _⦋0⦌,
    VertexIso (X := coconeMappingSpace F (coherentDiagramTotalVertex G))
      ((coconePointHomFamily (coherentDiagramTotalCocone F)
        (coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌) x)
      (coconeMappingPointAt (coherentTotalMapCocone F G a) (coherentDiagramTotalVertex G)
        (coherentTotalMapCocone_vertex F G a))

/-- 概要：元の全空間射の指定余錐を native な余極限写像で表す。
方針：余極限性から全 Hom 余錐族の本質的全射性を取り出す。
規約：指定余錐への比較同型を保持。使われ方：二射影の native な表示。 -/
def coherentTotalMapNativeRepresentation : CoherentTotalMapNativeRepresentation F G a :=
  Classical.choice <| by
  have h := (coconePointHomFamily_homotopyEquivalence (coherentDiagramTotalCocone F)
    (coherentDiagramTotalCocone_isColimit F) (coherentDiagramTotalVertex G)).isQCatEquivalence
  obtain ⟨x, ⟨e⟩⟩ := h.choose.isEssentiallySurjective
    (coconeMappingPointAt (coherentTotalMapCocone F G a) (coherentDiagramTotalVertex G)
      (coherentTotalMapCocone_vertex F G a))
  exact ⟨⟨x, e⟩⟩

/-- 概要：選択済み native 余極限写像の全空間比較は元の単位と具体的頂点射の合成に同型。
方針：指定余錐比較を全空間写像空間へ送り、元の指定射の比較へ続ける。
規約：native な射と指定比較をともに保持。使われ方：Kan 射との値の照合。 -/
def coherentTotalMapNativeComparisonIso :
    VertexIso (X := (SSet.uliftFunctor.{u + 1, u}).obj
      ((ihom (smallLeftUnstraightening F)).obj
        (spaceInfinityObject (coherentDiagramTotalVertex G)).obj))
      ((coconePointHomFamily (coherentDiagramTotalCocone F) (coherentDiagramTotalVertex G) ≫
        coherentCoconeTotalComparison F (coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
          (coherentTotalMapNativeRepresentation F G a).1)
      (ULift.up.{u + 1, u}
        (functorVertex (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G a))) :=
  (coherentTotalMapNativeRepresentation F G a).2.map
    (coherentCoconeTotalComparison F (coherentDiagramTotalVertex G)) ≪≫
      coherentTotalMapCoconeComparisonIso F G a

end SerrePositivity.InfinityCategories.F2
