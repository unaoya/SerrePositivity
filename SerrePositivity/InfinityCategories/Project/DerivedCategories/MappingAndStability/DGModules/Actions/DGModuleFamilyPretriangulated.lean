module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleSubcategoryPretriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGPretriangulatedQuasiEquivalence
public import SerrePositivity.DifferentialGraded.Category.Tensor
/-!
概要：重複を許す小さい実加群ラベル族の演算閉性から前三角性を判定する。
方針：同じ値の range への全 Hom 恒等な準同値を介し、D-8 b の一般判定を再利用する。
規約：零・shift・任意閉射 cone の厳密な値の被覆を明記する。
使われ方：c′ ゲート5のラベル模型への接続。被覆仮定の検証は別工程。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (I : Type w) [Small.{u} I] (value : I → ModuleCategory R D)

abbrev dgModuleFamilyRange := {M : ModuleCategory R D // M ∈ Set.range value}

def dgModuleFamilyRangeEvaluation :
    letI := inducedDGCategory R (fun i => ForgetEnrichment.to (Complex R) (value i))
    DGFunctor R I (dgModuleFamilyRange R D I value) := by
  letI := inducedDGCategory R (fun i => ForgetEnrichment.to (Complex R) (value i))
  exact { obj i := ⟨value i, i, rfl⟩
          map _ _ := 𝟙 _
          map_id _ := by simp; rfl
          map_comp _ _ _ := by simp; rfl }

lemma dgModuleFamilyRangeEvaluation_quasiEquivalence :
    letI := inducedDGCategory R (fun i => ForgetEnrichment.to (Complex R) (value i))
    QuasiEquivalence (dgModuleFamilyRangeEvaluation R D I value) := by
  letI := inducedDGCategory R (fun i => ForgetEnrichment.to (Complex R) (value i))
  refine ⟨fun _ _ => ?_, ⟨fun X => ?_⟩⟩
  · change QuasiIso (𝟙 _)
    infer_instance
  · obtain ⟨⟨M, i, rfl⟩⟩ := X
    exact ⟨(toHomotopy R I).obj (ForgetEnrichment.of (Complex R) i), ⟨Iso.refl _⟩⟩

lemma dgModuleFamily_isDGPretriangulated
    (hzero : ∃ i, value i = moduleZero R D)
    (hshift : ∀ i (s : ℤ), ∃ j, value j = (value i)⟦s⟧)
    (hcone : ∀ i j (f : value i ⟶ value j), ∃ k, value k = moduleCone R D f) :
    letI := inducedDGCategory R (fun i => ForgetEnrichment.to (Complex R) (value i))
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R I := by
  letI := inducedDGCategory R (fun i => ForgetEnrichment.to (Complex R) (value i))
  letI : Small.{u} {M : ModuleCategory R D // (Set.range value) M} := small_range value
  haveI : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (dgModuleFamilyRange R D I value) := by
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSubcategory_isDGPretriangulated R D (Set.range value)
    · obtain ⟨i, hi⟩ := hzero
      exact ⟨i, hi⟩
    · rintro M ⟨i, rfl⟩ s
      exact hshift i s
    · rintro M N ⟨i, rfl⟩ ⟨j, rfl⟩ f
      exact hcone i j f
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isDGPretriangulated_of_quasiEquivalence R I
    (dgModuleFamilyRange R D I value) (dgModuleFamilyRangeEvaluation R D I value)
    (dgModuleFamilyRangeEvaluation_quasiEquivalence R D I value)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
