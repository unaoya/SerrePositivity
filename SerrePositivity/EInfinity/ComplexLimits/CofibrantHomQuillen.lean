module

public import SerrePositivity.EInfinity.ComplexLimits.HomPostcomposeSurjective
public import SerrePositivity.EInfinity.ComplexLimits.CofibrantKProjective
public import SerrePositivity.EInfinity.ComplexLimits.AcyclicKernelQuasiIso
public import SerrePositivity.DifferentialGraded.Complexes.Closed
public import SerrePositivity.DifferentialGraded.Complexes.KProjectiveHom
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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory Limits HomologicalComplex CochainComplex HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

lemma homPostcompose_cofibrant_trivialFibration (P : Complex A)
    (hP : (projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ P)) {X Y : Complex A} (f : X ⟶ Y)
    (hf : projectiveFibrations A f) (hq : QuasiIso f) :
    projectiveFibrations A (homPostcompose P f) ∧ QuasiIso (homPostcompose P f) := by
  have hF := homPostcompose_cofibrant_fibration P hP f hf
  refine ⟨hF, ?_⟩
  have (n : ℤ) : Epi (f.f n) := (ModuleCat.epi_iff_surjective _).mpr (hf n)
  have : Epi f := epi_of_epi_f f inferInstance
  have hk : (kernel f).Acyclic := by
    have hs : (ShortComplex.mk _ _ (kernel.condition f)).ShortExact :=
      { exact := ShortComplex.exact_kernel f }
    exact hs.acyclic_X₁ hq
  have := projectiveCofibrant_isKProjective P hP
  have : (homFunctor P).IsRightAdjoint := (tensorRightHomAdjunction P).isRightAdjoint
  have hHom : (homComplex A P (kernel f)).Acyclic :=
    homComplex_acyclic_of_isKProjective A P (kernel f) hk
  have hkHom : (kernel ((homFunctor P).map f)).Acyclic :=
    SerrePositivity.cochainAcyclic_of_iso hHom
      (PreservesKernel.iso (homFunctor P) f)
  have (n : ℤ) : Epi ((homPostcompose P f).f n) :=
    (ModuleCat.epi_iff_surjective _).mpr (hF n)
  have : Epi (homPostcompose P f) := epi_of_epi_f _ inferInstance
  exact quasiIso_of_epi_acyclicKernel (homPostcompose P f) hkHom

lemma homFunctor_cofibrant_isRightQuillen (P : Complex A)
    (hP : (projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ P)) :
    letI := projectiveModelCategory A
    SerrePositivity.Quillen.IsRightQuillen (homFunctor P) := by
  let := projectiveModelCategory A
  constructor
  · intro X Y f hf
    exact homPostcompose_cofibrant_fibration P hP f hf
  · intro X Y f hf
    exact homPostcompose_cofibrant_trivialFibration P hP f hf.1 hf.2

end SerrePositivity.EInfinity.ComplexLimits
