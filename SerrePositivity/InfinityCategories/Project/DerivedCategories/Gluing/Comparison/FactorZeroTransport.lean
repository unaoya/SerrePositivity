module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Objects.FactorZeroObjects
public import SerrePositivity.DifferentialGraded.Module.Basic

/-! ホモトピー零対象の関手像、反対圏、および全 Hom 複体への移送。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits Opposite DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]

lemma dgGluingFactorIsZero_map {E : Type w} [DGCategory R E] (F : DGFunctor R C E)
    (x : C) (hx : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R C x) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R E (F.obj x) :=
  F.onHomotopy.map_isZero hx

/-- 元の H⁰ の零性は、同じ実恒等射と零射との dg 境界関係に等しい。 -/
lemma dgGluingFactorIsZero_iff_boundary (x : C) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R C x ↔
      boundaryRelation R C (𝟙 (ForgetEnrichment.of (Complex R) x)) 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero, IsZero.iff_id_eq_zero,
    ← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_zero,
    toHomotopy_map_eq_iff]

lemma dgGluingFactorIsZero_op (x : C) (hx : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R C x) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R Cᵒᵖ (op x) := by
  apply (dgGluingFactorIsZero_iff_boundary R Cᵒᵖ (op x)).2
  have h := (dgGluingFactorIsZero_iff_boundary R C x).1 hx
  exact h

/-- 零の標的への全 Hom 複体は、複体 dg 圏の H⁰ でも零。 -/
lemma dgGluingFactorIsZero_hom_target (x y : C) (hy : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R C y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R (Complex R) (homObject R C x y) :=
  dgGluingFactorIsZero_map R C (leftRepresentable R x) y hy

/-- 零の始域からの全 Hom 複体も、複体 dg 圏の H⁰ で零。 -/
lemma dgGluingFactorIsZero_hom_source (x y : C) (hx : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R C x) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R (Complex R) (homObject R C x y) :=
  dgGluingFactorIsZero_map R Cᵒᵖ (representable R y) (op x)
    (dgGluingFactorIsZero_op R C x hx)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
