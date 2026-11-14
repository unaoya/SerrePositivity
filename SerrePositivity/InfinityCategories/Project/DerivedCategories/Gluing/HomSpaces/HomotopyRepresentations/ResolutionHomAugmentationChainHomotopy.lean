module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.ResolutionHomAugmentationHomotopy

/-! 同じ比較 cochain は、二つの Hom 鎖写像の実鎖ホモトピーでもある。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)

def dgGluingResolutionHomAugmentationChainHomotopy :
    Homotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolutionHomOutputAugmentation R C E F X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolutionHomInputAugmentation R C E F X Y) :=
  (Cochain.equivHomotopy _ _).symm
    ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E F X Y, by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolutionHomAugmentation_boundary, Cochain.ofHom_sub, sub_add_cancel]⟩

lemma dgGluingResolutionHomOutputAugmentation_quasiIso
    [QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolutionHomInputAugmentation R C E F X Y)] :
    QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolutionHomOutputAugmentation R C E F X Y) := by
  constructor
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap,
    (dgGluingResolutionHomAugmentationChainHomotopy R C E F X Y).homologyMap_eq]
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
