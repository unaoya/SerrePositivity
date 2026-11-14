module
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations

/-! 代表加群間の K(D) の射を、元の同じ閉 dg 射へ持ち上げる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

/-- Yoneda の実 Hom 同型から、閉零圏の充満性を回収する。 -/
lemma dgGluingYonedaClosed_full : (dgYoneda R C).onClosed.Full :=
  (dgYoneda R C).onClosed_full_of_homIso (fun x y => by
    change IsIso (dgYonedaIso R x (representable R y)).inv
    infer_instance)

/-- 任意の代表加群間のホモトピー圏の射は、同じ閉 dg 射の像。 -/
lemma dgGluingYonedaHomotopy_map_surjective (X Y : C)
    (f : (moduleToHomotopy R C).obj (ForgetEnrichment.of (Complex R) (representable R X)) ⟶
      (moduleToHomotopy R C).obj (ForgetEnrichment.of (Complex R) (representable R Y))) :
    ∃ g : ForgetEnrichment.of (Complex R) X ⟶ ForgetEnrichment.of (Complex R) Y,
      (moduleToHomotopy R C).map ((dgYoneda R C).onClosed.map g) = f := by
  let := dgGluingYonedaClosed_full R C
  obtain ⟨f', rfl⟩ := (moduleToHomotopy R C).map_surjective f
  obtain ⟨g, rfl⟩ := (dgYoneda R C).onClosed.map_surjective f'
  exact ⟨g, rfl⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
