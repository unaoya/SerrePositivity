module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.ShiftObjectTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CommaComparisons.CommaBoundaryLift

/-! 標準両加群シフトと選んだ実 gluing 対象を、同じ代表射と全 dg 自然な境界で結ぶ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (n : ℤ)
  (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingShiftRepresentative R C X.left n)
  (q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingShiftRepresentative R D X.right n)
local notation "F" => Morita.kernelTensor R D C M
local notation "W" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftObjectFromRepresentatives R C D M X n p q
local notation "S" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelShiftObject R C D M X n
local notation "T" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M W
local notation "ph" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftRepresentativeHom R C X.left n p
local notation "qh" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftRepresentativeHom R D X.right n q

/-- 同じ両代表射の augmentation 正方形は、全加群の境界関係で可換。 -/
lemma dgGluingKernelShiftRepresentative_square :
    boundaryRelation R (RightModule R C)
      (ph ≫ (T).augmentation) ((S).augmentation ≫ (F).onClosed.map qh) := by
  apply (moduleHomotopy_nonempty_iff R C _ _).1
  apply (moduleToHomotopy_map_eq_iff R C _ _).1
  have he := (moduleToHomotopy_map_eq_iff R C _ _).2
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftObject_augmentation_transport R C D M X n p q)
  have hp := congrArg (fun a => a ≫ (moduleToHomotopy R C).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) q.obj)).inv) he
  simp only [← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftAugmentationCore,
    Category.assoc, Iso.hom_inv_id, Category.comp_id] at hp
  change (moduleToHomotopy R C).map (ph ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelLift R C D M W) =
    (moduleToHomotopy R C).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelShiftAugmentation R C D M X n ≫ (F).onClosed.map qh)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelLift]
  exact hp

/-- 標準シフト対象から同じ代表対象の kernel 表示への実閉 comma 射。 -/
def dgGluingKernelShiftRepresentativeMap :
    ForgetEnrichment.of (Complex R) S ⟶ ForgetEnrichment.of (Complex R) T :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaBoundaryLift R (RightModule R D) (RightModule R C) F S T qh ph
    (dgGluingKernelShiftRepresentative_square R C D M X n p q)

/-- source 成分は、選んだ同じ右シフト代表同型の順射を K(D) で回収。 -/
lemma dgGluingKernelShiftRepresentativeMap_source_homotopy :
    (moduleToHomotopy R D).map
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R (RightModule R D) (RightModule R C) F).onClosed.map
        (dgGluingKernelShiftRepresentativeMap R C D M X n p q)) = q.comparison.hom := by
  rw [dgGluingKernelShiftRepresentativeMap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaBoundaryLift_source]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftRepresentativeHom_map R D X.right n q

/-- replacement 成分も、同じ左シフト代表同型の順射を K(C) で回収。 -/
lemma dgGluingKernelShiftRepresentativeMap_replacement_homotopy :
    (moduleToHomotopy R C).map
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R (RightModule R D) (RightModule R C) F).onClosed.map
        (dgGluingKernelShiftRepresentativeMap R C D M X n p q)) = p.comparison.hom := by
  rw [dgGluingKernelShiftRepresentativeMap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaBoundaryLift_replacement]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftRepresentativeHom_map R C X.left n p

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
