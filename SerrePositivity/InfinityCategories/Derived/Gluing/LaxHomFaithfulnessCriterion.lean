module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomPullbackComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyIsoPrecomposition
public import SerrePositivity.InfinityCategories.Core.FullyFaithful

/-! 実 Hom 複体から F2 引き戻しへの比較の同値性は、元の比較の充満忠実性と同値。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
local notation "F" => dgGluingUniverseDerivedNerveLaxComparison R C D M

lemma dgGluingLaxHomMappingComparison_equivalence_iff (X Y : DGGluingObject R C D M) :
    IsSimplicialHomotopyEquivalence (dgGluingLaxHomMappingComparison R C D M X Y) ↔
    IsSimplicialHomotopyEquivalence
      (pinchedHomMap (F) (ULift.up (Simplex.vertex X)) (ULift.up (Simplex.vertex Y))) :=
  dgGluingHomotopyEquivalence_precomp_iso_iff
    (dgGluingUniverseHomMappingIso R C D M X Y).symm _

lemma dgGluingLaxHomPullbackComparison_equivalence_iff (X Y : DGGluingObject R C D M) :
    IsSimplicialHomotopyEquivalence (dgGluingLaxHomPullbackComparison R C D M X Y) ↔
      IsSimplicialHomotopyEquivalence (dgGluingLaxHomMappingComparison R C D M X Y) :=
  dgGluingHomotopyEquivalence_postcomp_iso_iff _
    (F2.laxPullbackMappingIso (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)
      ((F).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex X)))
      ((F).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex Y))))

lemma dgGluingUniverseDerivedNerveLaxComparison_fullyFaithful_iff :
    IsFullyFaithful (F) ↔ ∀ X Y : DGGluingObject R C D M,
      IsSimplicialHomotopyEquivalence (dgGluingLaxHomPullbackComparison R C D M X Y) := by
  constructor
  · intro h X Y
    apply (dgGluingLaxHomPullbackComparison_equivalence_iff R C D M X Y).2
    exact (dgGluingLaxHomMappingComparison_equivalence_iff R C D M X Y).2 (h _ _)
  · intro h
    rintro ⟨x⟩ ⟨y⟩
    obtain ⟨X, rfl⟩ := (Simplex.vertexEquiv (A := R)
      (D := DGGluingObject R C D M)).symm.surjective x
    obtain ⟨Y, rfl⟩ := (Simplex.vertexEquiv (A := R)
      (D := DGGluingObject R C D M)).symm.surjective y
    apply (dgGluingLaxHomMappingComparison_equivalence_iff R C D M X Y).1
    exact (dgGluingLaxHomPullbackComparison_equivalence_iff R C D M X Y).1 (h X Y)

end SerrePositivity.InfinityCategories
