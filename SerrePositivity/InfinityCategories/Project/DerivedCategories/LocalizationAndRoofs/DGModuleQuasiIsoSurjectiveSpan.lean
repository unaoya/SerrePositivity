module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGModuleQuasiIsoSpanMaps
public import SerrePositivity.DifferentialGraded.Module.Disk
/-!
概要：元の加群準同型から、両脚が次数別全射準同型となる同じ実 span を得る。
方針：非輪状 disk 項と直和包含の準同型性、同じ射影・包含の厳密等式を使う。
規約：元の準同型の全射性は不要。使われ方：任意の双加群準同型の実作用比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded HomologicalComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 同じ左脚は、全評価の全整数次数で全射。 -/
lemma dgModuleQuasiIsoSpanLeft_degree_surjective (M N : ModuleCategory R D) :
    moduleDegreewiseSurjective R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleQuasiIsoSpanLeft R D M N) := by
  intro x n
  apply (moduleSurjectiveAt_iff_epi R D x n _).2
  have : Epi ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleQuasiIsoSpanLeft R D M N)) := by
    change Epi ((moduleEvaluation R D x).map (moduleBiprodFst R D M (moduleDiskCover R D N)))
    rw [moduleBiprodFst_eval]
    infer_instance
  infer_instance
/-- 同じ左脚は、元の指定射によらず全評価で準同型。 -/
lemma dgModuleQuasiIsoSpanLeft_quasiIso (M N : ModuleCategory R D) :
    moduleQuasiIso R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleQuasiIsoSpanLeft R D M N) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleBiprodFst_quasiIso_of_acyclic R D M (moduleDiskCover R D N)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDiskCover_acyclic R D N)
/-- 同じ第一包含も、非輪状な被覆直和項により準同型。 -/
lemma dgModuleQuasiIsoSpan_inl_quasiIso (M N : ModuleCategory R D) :
    moduleQuasiIso R D (moduleBiprodInl R D M (moduleDiskCover R D N)) := by
  apply (moduleQuasiIso R D).of_postcomp (W' := moduleQuasiIso R D)
    (moduleBiprodInl R D M (moduleDiskCover R D N)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleQuasiIsoSpanLeft R D M N)
    (dgModuleQuasiIsoSpanLeft_quasiIso R D M N)
  change moduleQuasiIso R D ((moduleBinaryBicone R D M (moduleDiskCover R D N)).inl ≫
    (moduleBinaryBicone R D M (moduleDiskCover R D N)).fst)
  rw [BinaryBicone.inl_fst]
  exact (moduleQuasiIso R D).id_mem M
/-- 同じ右脚は、元の指定射によらず全評価の全整数次数で全射。 -/
lemma dgModuleQuasiIsoSpanRight_degree_surjective {M N : ModuleCategory R D} (f : M ⟶ N) :
    moduleDegreewiseSurjective R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleQuasiIsoSpanRight R D f) := by
  intro x n
  apply (moduleSurjectiveAt_iff_epi R D x n _).2
  have : Epi (((moduleEvaluation R D x).map
      (moduleBiprodInr R D M (moduleDiskCover R D N) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleQuasiIsoSpanRight R D f)).f n) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleQuasiIsoSpan_inr_right]
    exact (moduleSurjectiveAt_iff_epi R D x n _).1
      (moduleDiskCoverπ_degreewiseSurjective R D N x n)
  rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] at this
  exact epi_of_epi (((moduleEvaluation R D x).map
    (moduleBiprodInr R D M (moduleDiskCover R D N))).f n)
    (((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleQuasiIsoSpanRight R D f)).f n)
/-- 元の指定射が準同型なら、同じ右脚も準同型。 -/
lemma dgModuleQuasiIsoSpanRight_quasiIso {M N : ModuleCategory R D} (f : M ⟶ N)
    (hf : moduleQuasiIso R D f) : moduleQuasiIso R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleQuasiIsoSpanRight R D f) := by
  apply (moduleQuasiIso R D).of_precomp (W' := moduleQuasiIso R D)
    (moduleBiprodInl R D M (moduleDiskCover R D N)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleQuasiIsoSpanRight R D f)
    (dgModuleQuasiIsoSpan_inl_quasiIso R D M N)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleQuasiIsoSpan_inl_right]
  exact hf
/-- 任意の加群準同型は、二つの次数別全射準同型の実 span によって比較される。 -/
lemma dgModuleQuasiIso_surjective_span {M N : ModuleCategory R D} (f : M ⟶ N)
    (hf : moduleQuasiIso R D f) :
    ∃ (P : ModuleCategory R D) (p : P ⟶ M) (q : P ⟶ N),
      moduleDegreewiseSurjective R D p ∧ moduleQuasiIso R D p ∧
      moduleDegreewiseSurjective R D q ∧ moduleQuasiIso R D q :=
  ⟨_, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleQuasiIsoSpanLeft R D M N, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleQuasiIsoSpanRight R D f,
    dgModuleQuasiIsoSpanLeft_degree_surjective R D M N,
    dgModuleQuasiIsoSpanLeft_quasiIso R D M N,
    dgModuleQuasiIsoSpanRight_degree_surjective R D f,
    dgModuleQuasiIsoSpanRight_quasiIso R D f hf⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
