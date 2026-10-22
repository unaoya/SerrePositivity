module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ShiftObjectTransport
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaBoundaryLift

/-! 標準両加群シフトと選んだ実 gluing 対象を、同じ代表射と全 dg 自然な境界で結ぶ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X : DGGluingObject R C D M) (n : ℤ)
  (p : DGGluingShiftRepresentative R C X.left n)
  (q : DGGluingShiftRepresentative R D X.right n)
local notation "F" => Morita.kernelTensor R D C M
local notation "W" => dgGluingShiftObjectFromRepresentatives R C D M X n p q
local notation "S" => dgGluingKernelShiftObject R C D M X n
local notation "T" => dgGluingKernelObject R C D M W
local notation "ph" => dgGluingShiftRepresentativeHom R C X.left n p
local notation "qh" => dgGluingShiftRepresentativeHom R D X.right n q

/-- 同じ両代表射の augmentation 正方形は、全加群の境界関係で可換。 -/
lemma dgGluingKernelShiftRepresentative_square :
    boundaryRelation R (RightModule R C)
      (ph ≫ (T).augmentation) ((S).augmentation ≫ (F).onClosed.map qh) := by
  apply (moduleHomotopy_nonempty_iff R C _ _).1
  apply (moduleToHomotopy_map_eq_iff R C _ _).1
  have he := (moduleToHomotopy_map_eq_iff R C _ _).2
    (dgGluingShiftObject_augmentation_transport R C D M X n p q)
  have hp := congrArg (fun a => a ≫ (moduleToHomotopy R C).map
    (dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) q.obj)).inv) he
  simp only [← CategoryTheory.Functor.map_comp, dgGluingShiftAugmentationCore,
    Category.assoc, Iso.hom_inv_id, Category.comp_id] at hp
  change (moduleToHomotopy R C).map (ph ≫ dgGluingKernelLift R C D M W) =
    (moduleToHomotopy R C).map
      (dgGluingKernelShiftAugmentation R C D M X n ≫ (F).onClosed.map qh)
  rw [dgGluingKernelLift]
  exact hp

/-- 標準シフト対象から同じ代表対象の kernel 表示への実閉 comma 射。 -/
def dgGluingKernelShiftRepresentativeMap :
    ForgetEnrichment.of (Complex R) S ⟶ ForgetEnrichment.of (Complex R) T :=
  dgGluingCommaBoundaryLift R (RightModule R D) (RightModule R C) F S T qh ph
    (dgGluingKernelShiftRepresentative_square R C D M X n p q)

/-- source 成分は、選んだ同じ右シフト代表同型の順射を K(D) で回収。 -/
lemma dgGluingKernelShiftRepresentativeMap_source_homotopy :
    (moduleToHomotopy R D).map
      ((dgFunctorCommaSource R (RightModule R D) (RightModule R C) F).onClosed.map
        (dgGluingKernelShiftRepresentativeMap R C D M X n p q)) = q.comparison.hom := by
  rw [dgGluingKernelShiftRepresentativeMap, dgGluingCommaBoundaryLift_source]
  exact dgGluingShiftRepresentativeHom_map R D X.right n q

/-- replacement 成分も、同じ左シフト代表同型の順射を K(C) で回収。 -/
lemma dgGluingKernelShiftRepresentativeMap_replacement_homotopy :
    (moduleToHomotopy R C).map
      ((dgFunctorCommaReplacement R (RightModule R D) (RightModule R C) F).onClosed.map
        (dgGluingKernelShiftRepresentativeMap R C D M X n p q)) = p.comparison.hom := by
  rw [dgGluingKernelShiftRepresentativeMap, dgGluingCommaBoundaryLift_replacement]
  exact dgGluingShiftRepresentativeHom_map R C X.left n p

end SerrePositivity.InfinityCategories
