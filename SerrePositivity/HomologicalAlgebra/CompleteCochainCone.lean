module

public import SerrePositivity.HomologicalAlgebra.CochainCompleteDetection

/-!
# 完備化した射と写像錐の非輪状性

## 概要
二回完備化した射の擬同型性から、二回完備化した写像錐の非輪状性を得る。

## 方針
具体的な完備化と実導来圏の完備化の自然同型、および完備化の三角関手性を使う。

## 規約
BS 著者版 Proposition 6.2。任意の非有界な複体で述べる。

## 使われ方
完備底変換の零性の反映を、射の擬同型性の反映に移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- 概要：二回の具体的な主元完備化は二回の実導来完備化と自然に一致する。
方針：既存の一回の比較を二回 whisker する。
規約：BS 著者版 Proposition 6.2。使われ方：射と写像錐の比較。 -/
def repeatedCompletionComparison (a : R) :
    DerivedCategory.Q ⋙ (derivedComplexCompletionFunctor R a ⋙ derivedComplexCompletionFunctor R a) ≅
      (complexCompletionFunctor R a ⋙ complexCompletionFunctor R a) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedComplexCompletionComparison R a) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (derivedComplexCompletionComparison R a) ≪≫
    (Functor.associator _ _ _).symm

/-- 概要：二回完備化した射が擬同型なら、二回完備化した写像錐は非輪状。
方針：完備化の三角関手性と第一射が同型である完全三角形の第三項の零性を使う。
規約：BS 著者版 Proposition 6.2、非有界な複体。
使われ方：零性の検出から擬同型の反映へ進む。 -/
theorem repeatedCompletion_cone_homology_isZero_of_map_quasiIso
    (a : R) {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)
    (hf : QuasiIso ((complexCompletionFunctor R a).map
      ((complexCompletionFunctor R a).map f))) (i : ℤ) :
    IsZero (((complexCompletionFunctor R a).obj
      ((complexCompletionFunctor R a).obj (CochainComplex.mappingCone f))).homology i) := by
  let F := derivedComplexCompletionFunctor R a ⋙ derivedComplexCompletionFunctor R a
  let e := repeatedCompletionComparison (R := R) a
  letI := hf
  have hq : IsIso (DerivedCategory.Q.map ((complexCompletionFunctor R a).map
      ((complexCompletionFunctor R a).map f))) := inferInstance
  have hF : IsIso (F.map (DerivedCategory.Q.map f)) :=
    (NatIso.isIso_map_iff e f).mpr hq
  letI := hF
  let T := F.mapTriangle.obj
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f))
  have hT : T ∈ distTriang _ := F.map_distinguished _
    (DerivedCategory.mappingCone_triangle_distinguished f)
  have hz : IsZero (F.obj (DerivedCategory.Q.obj (CochainComplex.mappingCone f))) :=
    (CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁ T hT).mpr (by
      change IsIso (F.map (DerivedCategory.Q.map f)); infer_instance)
  have hzQ := hz.of_iso (e.app (CochainComplex.mappingCone f)).symm
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map_isZero hzQ).of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app
      ((complexCompletionFunctor R a).obj
        ((complexCompletionFunctor R a).obj (CochainComplex.mappingCone f)))).symm

end SerrePositivity.DerivedCompletion
