module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentRepresentationCocone
public import SerrePositivity.InfinityCategories.Core.PrecompositionEquivalence

/-!
概要：同じ指定全空間射を表す二つの元の native 余錐を比較する。
方針：元の標準全空間比較の充満忠実性で指定された二つの比較同型を反映する。
規約：両方の表現と余錐を保持。使われ方：元の三角形の長辺と元の写像余錐の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (z : SpaceInfinity.{u} _⦋0⦌)
  (a : smallLeftUnstraightening F ⟶ (spaceInfinityObject z).obj)

/-- 概要：同じ指定射の二表現の元の余錐の間の比較同型。
方針：標準比較の像で指定射を介して結び、充満忠実性で元の余錐へ戻す。
規約：元の二余錐の指定頂点を保持。使われ方：元の合成三角形の余錐比較。 -/
def coherentRepresentationCoconeIso (R S : CoherentConstantRepresentation F z a) :
    VertexIso (X := coconeMappingSpace F z)
      (coconeMappingPointAt (coherentRepresentationCocone F z a R) z
        (coherentRepresentationCocone_vertex F z a R))
      (coconeMappingPointAt (coherentRepresentationCocone F z a S) z
        (coherentRepresentationCocone_vertex F z a S)) :=
  (coherentCoconeTotalComparison_isQCatEquivalence F z).isFullyFaithful.preimageVertexIso
    (coherentRepresentationCoconeComparisonIso F z a R ≪≫
      (coherentRepresentationCoconeComparisonIso F z a S).symm)

end SerrePositivity.InfinityCategories.F2
