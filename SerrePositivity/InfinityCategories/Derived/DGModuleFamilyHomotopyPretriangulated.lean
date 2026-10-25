module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFamilyHomotopyCone
/-!
概要：重複ラベル族の実値のホモトピー cone 閉性から前三角性を判定する。
方針：零・shift・cone の代表を制限 Yoneda へ送り、D-8 b の一般判定を使う。
規約：cone の厳密な値の一致やラベルの単射性を仮定しない。
使われ方：c′ の同時精密化を通過した提示模型への b の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CategoryTheory.Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (I : Type w) [Small.{u} I] (value : I → RightModule R D)

lemma dgModuleFamily_isDGPretriangulated_of_homotopy_cones :
    letI := inducedDGCategory R value
    (∃ i, IsZero (ForgetEnrichment.of (Complex R) (value i))) →
    (∀ i (s : ℤ), ∃ j, Nonempty ((ForgetEnrichment.of (Complex R) (value i))⟦s⟧ ≅
      ForgetEnrichment.of (Complex R) (value j))) →
    (∀ {X Y : ClosedCategory R I} (f : X ⟶ Y), ∃ k,
      Nonempty ((moduleToHomotopy R D).obj
        (moduleCone R D ((inducedDGEvaluation R value).onClosed.map f)) ≅
          (moduleToHomotopy R D).obj (ForgetEnrichment.of (Complex R) (value k)))) →
    IsDGPretriangulated R I := by
  letI := inducedDGCategory R value
  rintro ⟨i, hi⟩ hshift hcone
  apply isDGPretriangulated_of_representable_operations R I
  · exact dgModuleFamilyRepresentables_containsZero R D I value i hi
  · intro X s
    obtain ⟨j, ⟨e⟩⟩ := hshift X s
    apply (dgRepresentableHomotopyProperty_iff R I _).mpr
    exact ⟨j, ⟨(moduleToHomotopy R I).mapIso
      (dgModuleFamilyShiftIso R D I value X j s e)⟩⟩
  · intro X Y f
    obtain ⟨k, hk⟩ := hcone f
    exact dgModuleFamilyYonedaCone_homotopyRepresentable R D I value f k hk

end SerrePositivity.InfinityCategories
