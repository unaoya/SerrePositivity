module

public import SerrePositivity.InfinityCategories.HomotopyLimits.LocalInitialComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.LocalPrismRestriction

/-!
概要：任意の coherent な図式の余極限間の指定比較辺が S-equivalence となる条件を証明する。
方針：全 Hom の比較のホモトピー可換性と同値の二対三則を使う。
規約：元の比較辺と余極限余錐を保持。使われ方：HTT 5.5.4.5(2) の余極限閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 余錐制限が固定終点で同値なら、指定された余極限比較辺の頂点への像は局所。 -/
lemma isLocalForHom_colimitRestriction_comparison {J K X : SSet.{u}} [Quasicategory X]
    (p : J ⟶ X) (i : K ⟶ J) (d : JoinCocone p) (hd : IsColimitCone d)
    (c : JoinCocone (i ≫ p)) (hc : IsColimitCone c)
    (e : (sliceUnder (i ≫ p)).Edge c ((sliceUnderRestrict p i).app (Opposite.op ⦋0⦌) d))
    (z : X _⦋0⦌) (h : IsQCatEquivalence (cosliceRestrictionFiberMap p i z)) :
    IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk
      (edgeCosliceEdge (SSet.yonedaEquiv.symm e.edge ≫ sliceUnderProjection (i ≫ p)))) z :=
  isLocalForHom_initialRestriction_of_fiber_equivalence
    (sliceUnderProjection p) (sliceUnderProjection (i ≫ p)) (sliceUnderRestrict p i)
      (sliceUnderRestrict_projection p i) d hd hc e z h

/-- 全局所対象への余錐制限が同値なら、元の余極限比較辺の頂点への像は S-equivalence。 -/
lemma localEquivalences_colimitRestriction_comparison {J K X : SSet.{u}} [Quasicategory X]
    (W : Set (X _⦋1⦌)) (p : J ⟶ X) (i : K ⟶ J)
    (d : JoinCocone p) (hd : IsColimitCone d) (c : JoinCocone (i ≫ p)) (hc : IsColimitCone c)
    (e : (sliceUnder (i ≫ p)).Edge c ((sliceUnderRestrict p i).app (Opposite.op ⦋0⦌) d))
    (h : ∀ z : X _⦋0⦌, IsLocalObject W z →
      IsQCatEquivalence (cosliceRestrictionFiberMap p i z)) :
    (e.map (sliceUnderProjection (i ≫ p))).edge ∈ localEquivalences W := by
  have he : (edgeCosliceEdge
      (SSet.yonedaEquiv.symm e.edge ≫ sliceUnderProjection (i ≫ p))).edge =
      (e.map (sliceUnderProjection (i ≫ p))).edge := by
    change SSet.yonedaEquiv (SSet.yonedaEquiv.symm e.edge ≫ _) = _
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    rfl
  rw [← he]
  apply (localEquivalenceHom_iff_edge_mem W _).mp
  intro z hz
  exact isLocalForHom_colimitRestriction_comparison p i d hd c hc e z (h z hz)

/-- 局所辺の prism の全図式から始点図式への、元の余極限比較辺は S-equivalence。 -/
lemma localEquivalences_colimitPrism_source_comparison {K X : SSet.{u}} [Quasicategory X]
    (W : Set (X _⦋1⦌)) (g : (Δ[1] : SSet.{u}) ⊗ K ⟶ X)
    (d : JoinCocone g) (hd : IsColimitCone d)
    (c : JoinCocone (prismEndpoint 0 K ≫ g)) (hc : IsColimitCone c)
    (e : (sliceUnder (prismEndpoint 0 K ≫ g)).Edge c
      ((sliceUnderRestrict g (prismEndpoint 0 K)).app (Opposite.op ⦋0⦌) d))
    (h : ∀ k : K _⦋0⦌, SSet.yonedaEquiv (prismVertexEvaluation g k) ∈ localEquivalences W) :
    (e.map (sliceUnderProjection (prismEndpoint 0 K ≫ g))).edge ∈ localEquivalences W := by
  apply localEquivalences_colimitRestriction_comparison W g (prismEndpoint 0 K) d hd c hc e
  intro z hz
  have := localPrism_source_cocones_trivial g z (fun k ↦
    ((localEquivalenceHom_iff_edge_mem W (edgeCosliceEdge (prismVertexEvaluation g k))).mpr
      (h k)) z hz)
  exact isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories.HomotopyLimits
