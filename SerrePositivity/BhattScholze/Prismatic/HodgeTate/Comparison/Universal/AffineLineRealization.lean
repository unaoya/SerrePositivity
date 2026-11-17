module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.ProjectiveHomologyLift
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFormsProjective
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.AffineTotalModel
public import Mathlib.Algebra.Homology.Additive
import all Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# 元の affine line の標準 HT 写像の実現

## 概要
元の零次・一次形式の single の直和から、元の指定された全複体への射を作る。

## 方針
元のホモロジー写像をそれぞれ持ち上げ、既存の直和でまとめる。

## 規約
零次・一次のホモロジー上の値は、元の affineHTTotalMap そのものである。
擬同型性はこの実現の存在だけから結論しない。

## 使われ方
BS Proposition 6.2 の射 η を、Construction 6.1 の反映へ渡す。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R]

private def homologyBiprodInlIso (K L : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    (hL : IsZero (L.homology i)) : K.homology i ≅ (K ⊞ L).homology i where
  hom := HomologicalComplex.homologyMap biprod.inl i
  inv := HomologicalComplex.homologyMap biprod.fst i
  hom_inv_id := by
    rw [← HomologicalComplex.homologyMap_comp, biprod.inl_fst, HomologicalComplex.homologyMap_id]
  inv_hom_id := by
    let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i
    have hz : H.map (biprod.snd : K ⊞ L ⟶ L) = 0 := hL.eq_of_tgt _ _
    have ht := congrArg H.map (show (biprod.fst : K ⊞ L ⟶ K) ≫ biprod.inl +
      (biprod.snd : K ⊞ L ⟶ L) ≫ biprod.inr = 𝟙 (K ⊞ L) from biprod.total)
    rw [H.map_id] at ht
    simp only [Functor.map_add, Functor.map_comp, hz, zero_comp, add_zero] at ht
    dsimp only [H, HomologicalComplex.homologyFunctor] at ht
    exact ht

private def homologyBiprodInrIso (K L : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    (hK : IsZero (K.homology i)) : L.homology i ≅ (K ⊞ L).homology i where
  hom := HomologicalComplex.homologyMap biprod.inr i
  inv := HomologicalComplex.homologyMap biprod.snd i
  hom_inv_id := by
    rw [← HomologicalComplex.homologyMap_comp, biprod.inr_snd, HomologicalComplex.homologyMap_id]
  inv_hom_id := by
    let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i
    have hz : H.map (biprod.fst : K ⊞ L ⟶ K) = 0 := hK.eq_of_tgt _ _
    have ht := congrArg H.map (show (biprod.fst : K ⊞ L ⟶ K) ≫ biprod.inl +
      (biprod.snd : K ⊞ L ⟶ L) ≫ biprod.inr = 𝟙 (K ⊞ L) from biprod.total)
    rw [H.map_id] at ht
    simp only [Functor.map_add, Functor.map_comp, hz, zero_comp, zero_add] at ht
    dsimp only [H, HomologicalComplex.homologyFunctor] at ht
    exact ht

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A)
local notation "R₁" => affineAlgebra P 1
local notation "M₀" => ModuleCat.of R₁ (affineForms P 1 0)
local notation "M₁" => ModuleCat.of R₁ (affineForms P 1 1)

/-- 元の零次・一次完備形式を、それぞれの元の次数に置いた直和複体。 -/
abbrev affineLineFormalModel : CochainComplex (ModuleCat.{u} R₁) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u} R₁) (.up ℤ) 0).obj M₀ ⊞
    (HomologicalComplex.single (ModuleCat.{u} R₁) (.up ℤ) 1).obj M₁

/-- 元の零次形式から同じ直和模型の零次ホモロジーへの指定同型。 -/
def affineLineFormalZeroIso : M₀ ≅ (affineLineFormalModel P).homology 0 :=
  (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 M₀).symm ≪≫
    homologyBiprodInlIso _ _ 0
      (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 1 M₁ 0 (by decide))

/-- 元の一次形式から同じ直和模型の一次ホモロジーへの指定同型。 -/
def affineLineFormalOneIso : M₁ ≅ (affineLineFormalModel P).homology 1 :=
  (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 1 M₁).symm ≪≫
    homologyBiprodInrIso _ _ 1
      (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 M₀ 1 (by decide))

/-- 元の affine line の二つの標準 HT 写像を、同じ直和模型からの射で同時に実現する。 -/
theorem exists_affineLine_HT_realization (hP : IsBoundedPrism P) :
    ∃ η : affineLineFormalModel P ⟶ affineHTTotalComplex P hP 1,
      (affineLineFormalZeroIso P).hom ≫ HomologicalComplex.homologyMap η 0 =
          ModuleCat.ofHom (affineHTTotalMap P hP 1 0) ∧
        (affineLineFormalOneIso P).hom ≫ HomologicalComplex.homologyMap η 1 =
          ModuleCat.ofHom (affineHTTotalMap P hP 1 1) := by
  haveI := affineForms_projective P 1 0
  haveI := affineForms_projective P 1 1
  obtain ⟨q₀, h₀⟩ := exists_single_homology_lift (affineHTTotalComplex P hP 1) (0 : ℤ) M₀
    (ModuleCat.ofHom (affineHTTotalMap P hP 1 0))
  obtain ⟨q₁, h₁⟩ := exists_single_homology_lift (affineHTTotalComplex P hP 1) (1 : ℤ) M₁
    (ModuleCat.ofHom (affineHTTotalMap P hP 1 1))
  refine ⟨biprod.desc q₀ q₁, ?_, ?_⟩
  · change ((HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 M₀).inv ≫
        HomologicalComplex.homologyMap biprod.inl 0) ≫
        HomologicalComplex.homologyMap (biprod.desc q₀ q₁) 0 = _
    rw [Category.assoc, ← HomologicalComplex.homologyMap_comp, biprod.inl_desc]
    exact h₀
  · change ((HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 1 M₁).inv ≫
        HomologicalComplex.homologyMap biprod.inr 1) ≫
        HomologicalComplex.homologyMap (biprod.desc q₀ q₁) 1 = _
    rw [Category.assoc, ← HomologicalComplex.homologyMap_comp, biprod.inr_desc]
    exact h₁

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
