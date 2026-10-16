module
public import SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleLocalization
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleSemifreeKFlat

/-! # 右相対K-flat部分圏の局所化から導来bimodule圏への対象の到達性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w)
  [DGCategory A C] [DGCategory A E] [Small.{u} C] [Small.{u} E]

def rightKFlatResolutionObj (hE : localHomKFlat A E) (M : BimoduleCategory A C E) :
    RightKFlatBimoduleCategory A C E :=
  ⟨(bimoduleCanonicalSemifreeResolution A C E M).obj,
    (bimoduleCanonicalSemifreeResolution A C E M).rightRelativeKFlat A C E hE⟩

def rightKFlatResolutionDerivedIso (hE : localHomKFlat A E) (M : BimoduleCategory A C E) :
    (rightKFlatDerivedInclusion A C E).obj
        ((rightKFlatToDerived A C E).obj (rightKFlatResolutionObj A C E hE M)) ≅
      (bimoduleToDerived A C E).obj M :=
  bimoduleDerivedIso A C E (bimoduleCanonicalSemifreeResolution A C E M).π
    (bimoduleCanonicalSemifreeResolution A C E M).quasiIso

/-- 本質的全射性のみ。充満忠実性をこの段階では仮定しない。 -/
lemma rightKFlatDerivedInclusion_essSurj (hE : localHomKFlat A E) :
    (rightKFlatDerivedInclusion A C E).EssSurj where
  mem_essImage X := by
    obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (bimoduleToDerived A C E) X
    exact ⟨(rightKFlatToDerived A C E).obj (rightKFlatResolutionObj A C E hE M),
      ⟨rightKFlatResolutionDerivedIso A C E hE M ≪≫ e⟩⟩

end SerrePositivity.DifferentialGraded.BimoduleTensor
