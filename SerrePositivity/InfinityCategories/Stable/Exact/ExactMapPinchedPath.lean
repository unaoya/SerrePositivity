module

public import SerrePositivity.InfinityCategories.Stable.Exact.ExactMapHomotopy
public import SerrePositivity.InfinityCategories.PinchedHom.Paths

/-!
概要：完全関手の比較同型を、StableInfinity の写像空間内の実際の道へ移す。
方針：core 内の比較の射を同じホモトピー類の辺で表し、coherent Hom 比較で写す。
規約：h StableInfinity の可換式だけに落とさない。使われ方：元の二脚の正方形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {A B : StableCategory.{u}} {F G : ExactMap A B} (h : FunctorIso F.hom G.hom)

def exactMapCoreEdge : SSet.Edge
    (X := SimplicialCategory.sHom (C := StableQCat.{u}) A B)
    (SimplicialCategory.homEquiv' (C := StableQCat.{u}) A B F)
    (SimplicialCategory.homEquiv' (C := StableQCat.{u}) A B G) :=
  SSet.Edge.ofTruncated (Classical.choose (homotopyCategory_homMk_surjective _ _
    (exactMapCoreVertexIso h).hom))

lemma exactMapCoreEdge_hom :
    Truncated.HomotopyCategory.homMk (exactMapCoreEdge h).toTruncated =
      (exactMapCoreVertexIso h).hom :=
  Classical.choose_spec (homotopyCategory_homMk_surjective _ _ (exactMapCoreVertexIso h).hom)

def stableArrowPinchedVertex (F : ExactMap A B) :
    (pinchedHom (stableVertex A) (stableVertex B)) _⦋0⦌ :=
  (PinchedHom.vertexEquiv _ _).symm (stableArrow F)

def exactMapPinchedPath : SSet.Edge
    (X := pinchedHom (stableVertex A) (stableVertex B))
    (stableArrowPinchedVertex F) (stableArrowPinchedVertex G) := by
  let e : SSet.Edge (X := (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (C := StableQCat.{u}) A B))
      (ULift.up (SimplicialCategory.homEquiv' (C := StableQCat.{u}) A B F))
      (ULift.up (SimplicialCategory.homEquiv' (C := StableQCat.{u}) A B G)) :=
    SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, u + 1} (exactMapCoreEdge h).toTruncated)
  let a := e.map (coherentHomComparison (C := StableQCat.{u}) A B)
  have hv (K : ExactMap A B) :
      (coherentHomComparison (C := StableQCat.{u}) A B).app (Opposite.op ⦋0⦌)
        (ULift.up (SimplicialCategory.homEquiv' (C := StableQCat.{u}) A B K)) =
          stableArrowPinchedVertex K := by
    apply (PinchedHom.vertexEquiv (stableVertex A) (stableVertex B)).injective
    calc
      _ = stableArrow K := by
        apply SSet.Edge.ext
        exact coherentHomComparison_ordinary (C := StableQCat.{u}) K
      _ = _ := (PinchedHom.vertexEquiv (stableVertex A) (stableVertex B)
        ).apply_symm_apply (stableArrow K) |>.symm
  exact a.ofEq (hv F) (hv G)

def exactMapComparisonTriangle :
    SSet.Edge.CompStruct (SSet.Edge.id (stableVertex A)) (stableArrow G) (stableArrow F) := by
  have t := PinchedHom.pathCompStruct (exactMapPinchedPath h)
  simpa only [stableArrowPinchedVertex, Equiv.apply_symm_apply] using t

end SerrePositivity.KST.LocalizingInvariants
