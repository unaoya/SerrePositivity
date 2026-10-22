module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeKernelModel
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaBoundaryLift

/-! 標準加群円錐と選んだ gluing 円錐対象を、同じ二つの代表射と全 dg 自然な境界で結ぶ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (p : DGGluingConeRepresentative R C Y.left Z.left (dgGluingConeLeftArrow R C D M Y Z f))
  (q : DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M Y Z f)))
local notation "W" => dgGluingConeObjectFromRepresentatives R C D M Y Z f p q
local notation "L" => dgGluingKernelConeObject R C D M Y Z f
local notation "T" => dgGluingKernelObject R C D M W
local notation "F" => Morita.kernelTensor R D C M
local notation "ph" => dgGluingConeRepresentativeHom R C Y.left Z.left
  (dgGluingConeLeftArrow R C D M Y Z f) p
local notation "qh" => dgGluingConeRepresentativeHom R D Y.right Z.right
  (CategoryTheory.Functor.map
    (SerrePositivity.DifferentialGraded.DGFunctor.onClosed (dgYoneda R D))
    (dgGluingConeRightArrow R C D M Y Z f)) q

/-- 両代表射の augmentation 正方形は、全 dg 自然な加群ホモトピーで可換する。 -/
lemma dgGluingKernelConeRepresentative_square :
    boundaryRelation R (RightModule R C)
      (ph ≫ (T).augmentation) ((L).augmentation ≫ (F).onClosed.map qh) := by
  apply (moduleHomotopy_nonempty_iff R C _ _).1
  apply (moduleToHomotopy_map_eq_iff R C _ _).1
  have he := (moduleToHomotopy_map_eq_iff R C _ _).2
    (dgGluingConeObject_augmentation_transport R C D M Y Z f p q)
  have hp := congrArg (fun a => a ≫ (moduleToHomotopy R C).map
    (dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) q.obj)).inv) he
  simp only [← CategoryTheory.Functor.map_comp, dgGluingConeAugmentationCore,
    Category.assoc, Iso.hom_inv_id, Category.comp_id] at hp
  change (moduleToHomotopy R C).map (ph ≫ dgGluingKernelLift R C D M W) =
    (moduleToHomotopy R C).map
      (dgGluingConeKernelMorphism R C D M Y Z f ≫ (F).onClosed.map qh)
  rw [dgGluingKernelLift, dgGluingConeKernelMorphism, Category.assoc]
  exact hp

/-- 標準加群円錐から、選んだ gluing 円錐対象の kernel 表示への同じ実閉 comma 射。 -/
def dgGluingKernelConeRepresentativeMap : ForgetEnrichment.of (Complex R) L ⟶
    ForgetEnrichment.of (Complex R) T :=
  dgGluingCommaBoundaryLift R (RightModule R D) (RightModule R C) F L T qh ph
    (dgGluingKernelConeRepresentative_square R C D M Y Z f p q)

/-- source 成分の K(D) の像は、選んだ同じ右円錐代表同型の射を回収する。 -/
lemma dgGluingKernelConeRepresentativeMap_source_homotopy :
    (moduleToHomotopy R D).map
      ((dgFunctorCommaSource R (RightModule R D) (RightModule R C) F).onClosed.map
        (dgGluingKernelConeRepresentativeMap R C D M Y Z f p q)) = q.comparison.hom := by
  rw [dgGluingKernelConeRepresentativeMap, dgGluingCommaBoundaryLift_source]
  exact dgGluingConeRepresentativeHom_map R D Y.right Z.right _ q

/-- replacement 成分の K(C) の像も、選んだ同じ左円錐代表同型の射を回収する。 -/
lemma dgGluingKernelConeRepresentativeMap_replacement_homotopy :
    (moduleToHomotopy R C).map
      ((dgFunctorCommaReplacement R (RightModule R D) (RightModule R C) F).onClosed.map
        (dgGluingKernelConeRepresentativeMap R C D M Y Z f p q)) = p.comparison.hom := by
  rw [dgGluingKernelConeRepresentativeMap, dgGluingCommaBoundaryLift_replacement]
  exact dgGluingConeRepresentativeHom_map R C Y.left Z.left _ p

end SerrePositivity.InfinityCategories
