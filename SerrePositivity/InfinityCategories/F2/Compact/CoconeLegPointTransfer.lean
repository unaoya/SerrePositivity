module

public import SerrePositivity.InfinityCategories.F2.Compact.CoconeLegComposition
public import SerrePositivity.InfinityCategories.F2.Compact.SpaceEdgeValueEquivalence
public import SerrePositivity.InfinityCategories.F2.Compact.PointRepresentativesComposition
public import SerrePositivity.InfinityCategories.F2.Compact.CoconeLegPointRepresentatives
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTotalColimit
public import SerrePositivity.InfinityCategories.F1.UniverseQCatEquivalence

/-!
概要：任意の指定余極限余錐の点を、元の同じ図式の値から同じ脚で成分まで回収する。
方針：標準余錐との余錐全体の同型を実際の辺で表し、元の合成三角形で移す。
規約：指定余錐を標準余錐へ置き換えず、元の各脚の実際の Kan 値を保持。
使われ方：compact 対象の Hom の指定余極限の恒等点を一つの項へ因子化する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}} {c d : JoinCocone F}

/-- 元の余錐の点が、同じ元の一つの値から同じ脚で成分まで回収できるという性質。 -/
def HasCoconeLegPointRepresentatives (c : JoinCocone F) : Prop :=
  ∀ x : ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject c.vertex).obj) _⦋0⦌,
    ∃ b : B _⦋0⦌,
      ∃ v : ((SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) b)).obj) _⦋0⦌,
        SSet.π₀.mk (((SSet.uliftFunctor.{u + 1, u}).map
          (spaceInfinityEdgeValue (coconeTransportLeg c b))).app (Opposite.op ⦋0⦌) v) =
            SSet.π₀.mk x

/-- 元の可逆な余錐辺と同じ全三角形は、同じ各脚による点回収を保つ。 -/
lemma hasCoconeLegPointRepresentatives_of_edge
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (sliceUnder F)) c d)
    (he : IsInvertibleEdge (X := sliceUnder F) e) (hc : HasCoconeLegPointRepresentatives c) :
    HasCoconeLegPointRepresentatives d := by
  have hv : IsInvertibleEdge (coconeVertexEdge e) := he.map (sliceUnderProjection F)
  let q : QCatEquivalence
      ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject c.vertex).obj)
      ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject d.vertex).obj) :=
    (spaceInfinityEdgeValue_isQCatEquivalence (coconeVertexEdge e) hv).ulift.choose
  apply componentRepresentative_of_triangle q
    (fun b => (SSet.uliftFunctor.{u + 1, u}).obj
      (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) b)).obj)
    (fun b => (SSet.uliftFunctor.{u + 1, u}).map
      (spaceInfinityEdgeValue (coconeTransportLeg c b)))
    (fun b => (SSet.uliftFunctor.{u + 1, u}).map
      (spaceInfinityEdgeValue (coconeTransportLeg d b)))
    _ hc
  intro b
  simpa only [Functor.map_comp, q, IsQCatEquivalence.choose] using
    uliftSimplicialHomotopy.{u, u + 1} (coconeLegCompositionHomotopy e b)

/-- 元の図式下の余錐全体の同型に沿い、同じ脚による点回収を移す。 -/
lemma hasCoconeLegPointRepresentatives_of_iso
    (i : VertexIso (X := sliceUnder F) c d) (hc : HasCoconeLegPointRepresentatives c) :
    HasCoconeLegPointRepresentatives d := by
  obtain ⟨e, he⟩ := homotopyCategory_homMk_surjective (X := sliceUnder F) c d i.hom
  have hi : IsInvertibleEdge (X := sliceUnder F) e := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk e)
    rw [he]
    infer_instance
  exact hasCoconeLegPointRepresentatives_of_edge e hi hc

/-- 任意の元の指定余極限余錐の全ての点を、元の同じ脚の作用で成分まで回収する。 -/
lemma colimitCoconeLeg_point_representative {I : SSet.{u}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ SpaceInfinity.{u})
    (c : JoinCocone D) (hc : IsColimitCone c) : HasCoconeLegPointRepresentatives c := by
  exact hasCoconeLegPointRepresentatives_of_iso
    (colimitConeIso (coherentDiagramTotalCocone D) c
      (coherentDiagramTotalCocone_isColimit D) hc)
    (coherentTotalCoconeLeg_point_representative D)

end SerrePositivity.InfinityCategories.F2.Compact
