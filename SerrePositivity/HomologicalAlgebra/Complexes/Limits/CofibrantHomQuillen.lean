module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.HomPostcomposeSurjective
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.CofibrantKProjective
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.AcyclicKernelQuasiIso
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import SerrePositivity.DifferentialGraded.Complexes.TensorShift
public import SerrePositivity.HomotopicalAlgebra.Quillen.Adjunction

/-!
# cofibrant 始域からの実内部 Hom の右 Quillen 性

概要：元の cofibrant P の Hom 関手は実射影 right Quillen。
方針：次数別射影性で全射を保ち、実 kernel 比較と K-projective 性で擬同型を保つ。
規約：非有界複体に追加のモデル仮定を課さない。
使われ方：閉随伴によるテンソルの左 Quillen 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.CochainComplex _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

lemma homPostcompose_cofibrant_trivialFibration (P : Complex A)
    (hP : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ P)) {X Y : Complex A} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A f) (hq : QuasiIso f) :
    _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A (homPostcompose P f) ∧ QuasiIso (homPostcompose P f) := by
  have hF := _root_.SerrePositivity.ComplexLimits.homPostcompose_cofibrant_fibration P hP f hf
  refine ⟨hF, ?_⟩
  have (n : ℤ) : Epi (f.f n) := (ModuleCat.epi_iff_surjective _).mpr (hf n)
  have : Epi f := epi_of_epi_f f inferInstance
  have hk : (kernel f).Acyclic := by
    have hs : (ShortComplex.mk _ _ (kernel.condition f)).ShortExact :=
      { exact := ShortComplex.exact_kernel f }
    exact hs.acyclic_X₁ hq
  have := _root_.SerrePositivity.ComplexLimits.projectiveCofibrant_isKProjective P hP
  have : (homFunctor P).IsRightAdjoint := (tensorRightHomAdjunction P).isRightAdjoint
  have hHom : (homComplex A P (kernel f)).Acyclic :=
    homComplex_acyclic_of_isKProjective A P (kernel f) hk
  have hkHom : (kernel ((homFunctor P).map f)).Acyclic :=
    SerrePositivity.cochainAcyclic_of_iso hHom
      (PreservesKernel.iso (homFunctor P) f)
  have (n : ℤ) : Epi ((homPostcompose P f).f n) :=
    (ModuleCat.epi_iff_surjective _).mpr (hF n)
  have : Epi (homPostcompose P f) := epi_of_epi_f _ inferInstance
  exact _root_.SerrePositivity.ComplexLimits.quasiIso_of_epi_acyclicKernel (homPostcompose P f) hkHom

lemma homFunctor_cofibrant_isRightQuillen (P : Complex A)
    (hP : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ P)) :
    letI := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    SerrePositivity.Quillen.IsRightQuillen (homFunctor P) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  constructor
  · intro X Y f hf
    exact _root_.SerrePositivity.ComplexLimits.homPostcompose_cofibrant_fibration P hP f hf
  · intro X Y f hf
    exact _root_.SerrePositivity.ComplexLimits.homPostcompose_cofibrant_trivialFibration P hP f hf.1 hf.2

end SerrePositivity.ComplexLimits
