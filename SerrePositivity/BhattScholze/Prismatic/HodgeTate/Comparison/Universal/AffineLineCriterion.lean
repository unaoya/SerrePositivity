module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineRealization
import all Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# 元の affine line の射の実現による判定

## 概要
元の直和模型の零次・一次以外のホモロジーは零であり、標準写像を実現する射が擬同型なら元の加群比較が従う。

## 方針
元の直和の射影・包含による恒等式をホモロジーへ移す。

## 規約
射の擬同型性は別に証明する必要がある。実現の存在を擬同型性と取り違えない。

## 使われ方
Construction 6.1 の保存性で検出した射を、元の affineLine_moduleComparison の型へ戻す。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A)

/-- 元の affine line の直和模型は、零次・一次以外のホモロジーを持たない。 -/
theorem affineLineFormal_homology_isZero (i : ℤ) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    IsZero ((affineLineFormalModel P).homology i) := by
  let R := affineAlgebra P 1
  let M₀ := ModuleCat.of R (affineForms P 1 0)
  let M₁ := ModuleCat.of R (affineForms P 1 1)
  let K := (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj M₀
  let L := (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 1).obj M₁
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i
  have hk : IsZero (K.homology i) := HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 M₀ i h0
  have hl : IsZero (L.homology i) := HomologicalComplex.isZero_single_obj_homology (.up ℤ) 1 M₁ i h1
  have hf : H.map (biprod.fst : K ⊞ L ⟶ K) = 0 := hk.eq_of_tgt _ _
  have hs : H.map (biprod.snd : K ⊞ L ⟶ L) = 0 := hl.eq_of_tgt _ _
  apply (IsZero.iff_id_eq_zero _).mpr
  have ht := congrArg H.map (show (biprod.fst : K ⊞ L ⟶ K) ≫ biprod.inl +
    (biprod.snd : K ⊞ L ⟶ L) ≫ biprod.inr = 𝟙 (K ⊞ L) from biprod.total)
  rw [H.map_id] at ht
  simp only [Functor.map_add, Functor.map_comp, hf, hs, zero_comp, zero_add] at ht
  dsimp only [H, HomologicalComplex.homologyFunctor] at ht
  exact ht.symm

/-- 元の標準写像の実現が擬同型なら、元の affine line の加群比較が成立する。 -/
theorem affineLine_moduleComparison_of_realization (hP : IsBoundedPrism P)
    (η : affineLineFormalModel P ⟶ affineHTTotalComplex P hP 1) [QuasiIso η]
    (h0 : (affineLineFormalZeroIso P).hom ≫ HomologicalComplex.homologyMap η 0 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 0))
    (h1 : (affineLineFormalOneIso P).hom ≫ HomologicalComplex.homologyMap η 1 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 1)) :
    Function.Bijective (hodgeTateMapZero P hP 1) ∧ Function.Bijective (hodgeTateMapOne P hP 1) ∧
      ∀ i : ℕ, 1 < i → Subsingleton (hodgeTateCohomology' P hP 1 i) := by
  have hi0 : IsIso (ModuleCat.ofHom (affineHTTotalMap P hP 1 0)) := by
    rw [← h0]
    infer_instance
  have hi1 : IsIso (ModuleCat.ofHom (affineHTTotalMap P hP 1 1)) := by
    rw [← h1]
    infer_instance
  have hb0 := (affineHTMap_bijective_iff P hP 1 0).mp
    ((affineHTTotalMap_bijective_iff P hP 1 0).mp
      ((ConcreteCategory.isIso_iff_bijective _).mp hi0))
  have hb1 := (affineHTMap_bijective_iff P hP 1 1).mp
    ((affineHTTotalMap_bijective_iff P hP 1 1).mp
      ((ConcreteCategory.isIso_iff_bijective _).mp hi1))
  refine ⟨?_, ?_, ?_⟩
  · have h := hb0.comp (degreeZeroForm P 1).bijective
    change Function.Bijective (fun x => (hodgeTateMap P hP 1).app 0 (degreeZeroForm P 1 x)) at h
    simpa only [(hodgeTateMap P hP 1).on_zero] using h
  · simpa only [(hodgeTateMap P hP 1).on_one] using hb1
  · intro i hi
    letI := htModule P hP 1 i
    have hz : IsZero ((affineHTTotalComplex P hP 1).homology (i : ℤ)) :=
      (affineLineFormal_homology_isZero P (i : ℤ) (by omega) (by omega)).of_iso
        (asIso (HomologicalComplex.homologyMap η (i : ℤ))).symm
    letI := ModuleCat.subsingleton_of_isZero hz
    exact (affineHTTotalCohomologyEquiv P hP 1 i).injective.subsingleton

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
