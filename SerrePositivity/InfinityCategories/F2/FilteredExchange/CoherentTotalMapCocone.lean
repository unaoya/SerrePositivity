module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentConstantCoconeComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTotalMap
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoTransport

/-!
概要：全空間の射を、元の余極限頂点を持つ指定余錐に接続する。
方針：標的の元の単位との合成を実現し、単位の自然性で像を正規化する。
規約：元の全空間射と単位を保持。使われ方：引き戻しの二射影の余錐表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})
  (a : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G)

/-- 概要：全空間射の後に標的の単位を続ける元の図式上の余錐。
方針：元の合成を表す native 余錐を実現。
規約：元の標的余極限頂点。使われ方：二射影の余錐表示。 -/
def coherentTotalMapCocone : JoinCocone F :=
  coherentConstantCocone F (coherentDiagramTotalVertex G) (a ≫ coherentDiagramTotalUnit G)

/-- 概要：写像余錐の頂点は標的の元の余極限頂点。
方針：指定頂点の実現。規約：厳密な等式。使われ方：標準余錐比較への入力。 -/
lemma coherentTotalMapCocone_vertex :
    (coherentTotalMapCocone F G a).vertex = coherentDiagramTotalVertex G :=
  coherentConstantCocone_vertex _ _ _

/-- 概要：写像余錐の標準比較の像は元の単位と余極限頂点の射の合成に同型。
方針：指定射の比較と単位の厳密な自然性。
規約：選んだ余錐と指定射を保持。使われ方：余極限写像の作用の照合。 -/
def coherentTotalMapCoconeComparisonIso :
    VertexIso (X := (SSet.uliftFunctor.{u + 1, u}).obj
      ((ihom (smallLeftUnstraightening F)).obj
        (spaceInfinityObject (coherentDiagramTotalVertex G)).obj))
      ((coherentCoconeTotalComparison F (coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
        (coconeMappingPointAt (coherentTotalMapCocone F G a) (coherentDiagramTotalVertex G)
          (coherentTotalMapCocone_vertex F G a)))
      (ULift.up.{u + 1, u}
        (functorVertex (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G a))) := by
  simpa only [coherentTotalVertexMap_unit, coherentTotalMapCocone] using
    coherentConstantCoconeComparisonIso F (coherentDiagramTotalVertex G)
      (a ≫ coherentDiagramTotalUnit G)

/-- 概要：写像余錐の実際の fiber 評価は元の単位と頂点射の合成に同型。
方針：全空間の比較を保ち、単位の自然性を持ち上げる。
規約：大きい全空間からの実際の射。使われ方：全 Hom の作用比較。 -/
def coherentTotalMapCoconeFiberIso :
    FunctorIso (coconeFiberValueMapAt (coherentTotalMapCocone F G a)
      (coherentDiagramTotalVertex G) (coherentTotalMapCocone_vertex F G a))
      (coherentLargeTotalUnit F ≫
        (SSet.uliftFunctor.{u + 1, u}).map (coherentTotalVertexMap F G a)) := by
  have e := coherentConstantCoconeFiberIso F (coherentDiagramTotalVertex G)
    (a ≫ coherentDiagramTotalUnit G)
  apply functorIsoOfEq e rfl
  rw [← coherentTotalVertexMap_unit, Functor.map_comp]
  rfl

end SerrePositivity.InfinityCategories.F2
