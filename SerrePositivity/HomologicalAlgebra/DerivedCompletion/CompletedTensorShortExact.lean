module

public import SerrePositivity.HomologicalAlgebra.DerivedTensorFixedModuleModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerDerivedComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionTriangulated
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# 短完全列の完備導来テンソルの零対象判定

## 概要
短完全列に固定加群を完備導来テンソルした実射について、三角形の零対象判定を与える。
## 方針
固定係数の既存射影分解モデルの自然性を使い、完全三角形の射を元の実射と照合する。
## 規約
任意の可換環・完備化元を許す。係数の平坦性や完備性を仮定しない。
## 使われ方
BS 著者版 Lemma 10.3（印刷 pp.78–79）の核と商の混合積に使う。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R) (C : ModuleCat.{u} R)

/--
## 概要
短完全列の完備導来テンソルの第二射が同型なら、第一対象は零である。
## 方針
固定射影分解との自然同型で完全三角形へ移し、第二射の同型性から結論する。
## 規約
仮定の射は元の導来テンソル関手による実射である。
## 使われ方
BS Lemma 10.3（著者版 pp.78–79）の核と商の混合積の消滅を導く。
-/
theorem completedTensor_isZero_of_shortExact_rightMap_isIso
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (hg : IsIso ((derivedComplexCompletionFunctor R a).map
      ((boundedAboveDerivedTensorModuleFunctor C).map S.g))) :
    IsZero ((derivedComplexCompletionFunctor R a).obj
      ((boundedAboveDerivedTensorModuleFunctor C).obj S.X₁)) := by
  let F := derivedComplexCompletionFunctor R a
  let K := extRes (projectiveResolution C)
  have hs := moduleTensorCochain_shortExact K (moduleCoefficientResolution_flat C) S hS
  let T := F.mapTriangle.obj (DerivedCategory.triangleOfSES hs)
  have hd : T ∈ distTriang _ := F.map_distinguished _
    (DerivedCategory.triangleOfSES_distinguished hs)
  let e₂ := F.mapIso (derivedTensorCoefficientModelIso C S.X₂)
  let e₃ := F.mapIso (derivedTensorCoefficientModelIso C S.X₃)
  have hn : F.map ((boundedAboveDerivedTensorModuleFunctor C).map S.g) ≫ e₃.hom =
      e₂.hom ≫ T.mor₂ := by
    exact (by simpa [Functor.map_comp, Functor.mapIso_hom, e₂, e₃, T,
      DerivedCategory.triangleOfSES] using
      congrArg F.map (derivedTensorCoefficientModelIso_naturality C S.g))
  have : IsIso (e₂.hom ≫ T.mor₂) := by rw [← hn]; infer_instance
  have : IsIso T.mor₂ := IsIso.of_isIso_comp_left e₂.hom T.mor₂
  exact (T.isZero₁_of_isIso₂ hd inferInstance).of_iso
    (F.mapIso (derivedTensorCoefficientModelIso C S.X₁))

/--
## 概要
短完全列の完備導来テンソルの第三対象が零なら、第一射は同型である。
## 方針
固定係数の自然な射影分解モデルの完全三角形で判定し、元の実射へ戻す。
## 規約
第三対象の消滅をホモロジーの一部の消滅で代用しない。
## 使われ方
BS Lemma 10.3（著者版 pp.78–79）の核の自己積に使う。
-/
theorem completedTensor_shortExact_leftMap_isIso_of_isZero
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (hz : IsZero ((derivedComplexCompletionFunctor R a).obj
      ((boundedAboveDerivedTensorModuleFunctor C).obj S.X₃))) :
    IsIso ((derivedComplexCompletionFunctor R a).map
      ((boundedAboveDerivedTensorModuleFunctor C).map S.f)) := by
  let F := derivedComplexCompletionFunctor R a
  let K := extRes (projectiveResolution C)
  have hs := moduleTensorCochain_shortExact K (moduleCoefficientResolution_flat C) S hS
  let T := F.mapTriangle.obj (DerivedCategory.triangleOfSES hs)
  have hd : T ∈ distTriang _ := F.map_distinguished _
    (DerivedCategory.triangleOfSES_distinguished hs)
  have hz' : IsZero T.obj₃ := hz.of_iso
    (F.mapIso (derivedTensorCoefficientModelIso C S.X₃)).symm
  have : IsIso T.mor₁ := (T.isZero₃_iff_isIso₁ hd).mp hz'
  let e₁ := F.mapIso (derivedTensorCoefficientModelIso C S.X₁)
  let e₂ := F.mapIso (derivedTensorCoefficientModelIso C S.X₂)
  have hn : F.map ((boundedAboveDerivedTensorModuleFunctor C).map S.f) ≫ e₂.hom =
      e₁.hom ≫ T.mor₁ := by
    exact (by simpa [Functor.map_comp, Functor.mapIso_hom, e₁, e₂, T,
      DerivedCategory.triangleOfSES] using
      congrArg F.map (derivedTensorCoefficientModelIso_naturality C S.f))
  have : IsIso (F.map ((boundedAboveDerivedTensorModuleFunctor C).map S.f) ≫ e₂.hom) := by
    rw [hn]; infer_instance
  exact IsIso.of_isIso_comp_right
    (F.map ((boundedAboveDerivedTensorModuleFunctor C).map S.f)) e₂.hom

end SerrePositivity.DerivedCompletion
