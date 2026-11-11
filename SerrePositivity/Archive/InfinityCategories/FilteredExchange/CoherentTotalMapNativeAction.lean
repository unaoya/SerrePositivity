module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalMapNative
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentCoconeTransportAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalMapNativeActionComponents

/-!
概要：元の native 余極限写像の輸送作用を、元の単位と具体的な Kan 頂点射へ比較する。
方針：元の全 Hom の輸送同型を native な射で評価し、指定余錐の比較を合成する。
規約：同じ native な射と指定比較。使われ方：元の単位による前合成の消去。
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

/-- 概要：選択済み native 余極限写像の、元の余錐と合成した実際の輸送作用。
方針：全 Hom 輸送作用を元の native な射で評価して射へ戻す。
規約：元の輸送族を使用。使われ方：具体的な Kan 射との作用の照合。 -/
def coherentTotalMapNativeAction : leftUnstraightening F ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject (coherentDiagramTotalVertex G)).obj :=
  (functorVertexEquiv _ _).symm
    ((coherentCoconeTransportAction F (coherentDiagramTotalCocone F)
      (coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
        (coherentTotalMapNativeRepresentation F G a).1)

/-- 概要：元の native 射の輸送作用は元の単位と具体的頂点射の合成に同型。
方針：全族の指定輸送同型の成分と指定余錐の全空間比較を続ける。
規約：実際の射の指定同型。使われ方：前合成の同値性で頂点側の作用を回収。 -/
def coherentTotalMapNativeActionIso :
    FunctorIso (coherentTotalMapNativeAction F G a)
      (coherentLargeTotalUnit F ≫
        (SSet.uliftFunctor.{u + 1, u}).map (coherentTotalVertexMap F G a)) := by
  exact vertexIsoOfEq (coherentTotalMapNativeActionComponentsIso F G a)
    ((functorVertexEquiv _ _).apply_symm_apply _).symm
    (congrArg functorVertex (coherentTotalMapNativeActionComponents_target F G a))

end SerrePositivity.InfinityCategories.F2
