module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitPointedCommonEndpoint
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitTetrahedronSides
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitTetrahedronFirstEdges

/-!
概要：最後の元の単位三単体の長辺側面と終端側面の実終点を厳密に同定する。
方針：元の二つの上単位三角形と指定第一辺を、共通終点の全パラメータ判定へ渡す。
規約：元の図式・実終点を保持。使われ方：最後の三単体の指定比較の三関係。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)

/-- 最後の元の三単体の二つの側面の実終点は、全選択を通じて同じ射。 -/
lemma coherentColimitUnitLastEndpoints_eq :
    coherentColimitUnitPointedFixedFaceEndpoint B T 2 1 (by decide)
      (coherentColimitUnitUpperTriangle B d) (coherentColimitUnitTetrahedron_lower_long B T) =
      coherentColimitUnitZeroFaceEndpoint B T 2 l
        (coherentColimitUnitTetrahedron_last_firstEdge B T)
        (coherentColimitUnitUpperTriangle B r) (coherentColimitUnitTetrahedron_lower_last B T) :=
  coherentColimitUnitPointedFixedFaceEndpoint_eq_zeroFace B T 2 1 (by decide)
    (coherentColimitUnitUpperTriangle B d) (coherentColimitUnitTetrahedron_lower_long B T)
    l (coherentColimitUnitTetrahedron_last_firstEdge B T)
    (coherentColimitUnitUpperTriangle B r) (coherentColimitUnitTetrahedron_lower_last B T)
    (by decide)

end SerrePositivity.InfinityCategories.F2
