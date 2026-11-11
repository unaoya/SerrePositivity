module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionStrictLiftStages
/-!
概要：整合する全 cell 段の strict lift を実余極限へ降下する。
方針：初期 disk 被覆と後続 kernel cell の実持ち上げ・余極限の普遍性を使う。
規約：augmentation と各段への制限は厳密。使われ方：双加群模型の strict lift。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (M : ModuleCategory R D) {T N : ModuleCategory R D} (g : M ⟶ N) (q : T ⟶ N)
  (hqs : moduleDegreewiseSurjective R D q) (hqq : moduleQuasiIso R D q)
def dgModuleResolutionStrictLiftCocone : Cocone (moduleResolutionDiagram R D M) where
  pt := T
  ι := NatTrans.ofSequence
    (fun n => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionStrictLiftStages R D M g q hqs hqq n).val) (by
      intro n
      simp only [moduleResolutionDiagram, Functor.comp_map, Over.forget_map,
        moduleResolutionOverDiagram, Functor.ofSequence_map_homOfLE_succ,
        Functor.const_obj_map]
      exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionStrictLiftStages_succ R D M g q hqs hqq n).trans
        (Category.comp_id _).symm)
def dgModuleResolutionStrictLift : moduleResolutionCandidate R D M ⟶ T :=
  colimit.desc _ (dgModuleResolutionStrictLiftCocone R D M g q hqs hqq)
lemma dgModuleResolutionStrictLift_ι (n : ℕ) :
    moduleResolutionCandidateι R D M n ≫ dgModuleResolutionStrictLift R D M g q hqs hqq =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionStrictLiftStages R D M g q hqs hqq n).val :=
  colimit.ι_desc (dgModuleResolutionStrictLiftCocone R D M g q hqs hqq) n
lemma dgModuleResolutionStrictLift_fac :
    dgModuleResolutionStrictLift R D M g q hqs hqq ≫ q =
      moduleResolutionCandidateπ R D M ≫ g := by
  apply colimit.hom_ext (F := moduleResolutionDiagram R D M)
  intro n
  change moduleResolutionCandidateι R D M n ≫
      (dgModuleResolutionStrictLift R D M g q hqs hqq ≫ q) =
    moduleResolutionCandidateι R D M n ≫ (moduleResolutionCandidateπ R D M ≫ g)
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionStrictLiftStages R D M g q hqs hqq n).val ≫ q := by
      rw [← Category.assoc, dgModuleResolutionStrictLift_ι]
    _ = (moduleResolutionStage R D M n).hom ≫ g :=
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionStrictLiftStages R D M g q hqs hqq n).property
    _ = (moduleResolutionCandidateι R D M n ≫ moduleResolutionCandidateπ R D M) ≫ g :=
      (congrArg (fun c => c ≫ g) (moduleResolutionCandidateι_π R D M n)).symm
    _ = _ := Category.assoc _ _ _
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
