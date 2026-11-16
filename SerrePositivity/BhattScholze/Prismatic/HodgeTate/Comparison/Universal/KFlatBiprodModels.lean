module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.TorAcyclicSingleDegrees
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# 同じ二本の模型の直和とK-flat性

## 概要
元の二本のK-flat模型の直和を使い、元の二次数の形式の模型を計算する。

## 方針
有限直和とテンソル・ホモロジーの標準同型を使い、同じ二本の射の擬同型性を移す。

## 規約
元の複体自体のK-flat性は要求しない。模型の射を実際に指定する。

## 使われ方
元のηの始域の零次・一次形式を、同じ直和の模型で検査する。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A B : Type u} [CommRing A] [CommRing B]

/-- 元の加法的関手について、既存の有限直和の保存を二項直和へ接続する。 -/
theorem additive_preservesBinaryBiproducts_model {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] : PreservesBinaryBiproducts F :=
  preservesBinaryBiproducts_of_preservesBiproducts F

attribute [local instance] additive_preservesBinaryBiproducts_model

/-- 加法的な関手の元の直和同型は、同じ直和の射と可換。 -/
theorem mapBiprod_map_square (F : Complex A ⥤ Complex B) [F.Additive]
    {K₀ K₁ L₀ L₁ : Complex A} (f₀ : K₀ ⟶ L₀) (f₁ : K₁ ⟶ L₁) :
    F.map (biprod.map f₀ f₁) ≫ (F.mapBiprod L₀ L₁).hom =
      (F.mapBiprod K₀ K₁).hom ≫ biprod.map (F.map f₀) (F.map f₁) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst, biprod.lift_fst_assoc, biprod.map_fst, ← F.map_comp]
  · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_snd, biprod.lift_snd_assoc, biprod.map_snd, ← F.map_comp]

/-- 同じ二本の擬同型の直和の射も擬同型。 -/
theorem quasiIso_biprod_map_model {K₀ K₁ L₀ L₁ : Complex A}
    (f₀ : K₀ ⟶ L₀) (f₁ : K₁ ⟶ L₁) [QuasiIso f₀] [QuasiIso f₁] :
    QuasiIso (biprod.map f₀ f₁) := by
  rw [quasiIso_iff]
  intro n
  apply (quasiIsoAt_iff_isIso_homologyMap _ _).mpr
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) n
  haveI : IsIso (H.map f₀) := by
    change IsIso (HomologicalComplex.homologyMap f₀ n)
    infer_instance
  haveI : IsIso (H.map f₁) := by
    change IsIso (HomologicalComplex.homologyMap f₁ n)
    infer_instance
  haveI : IsIso (biprod.map (H.map f₀) (H.map f₁)) := by
    change IsIso ((biprod.mapIso (asIso (H.map f₀)) (asIso (H.map f₁))).hom)
    infer_instance
  have hc : H.map (biprod.map f₀ f₁) ≫ (H.mapBiprod L₀ L₁).hom =
      (H.mapBiprod K₀ K₁).hom ≫ biprod.map (H.map f₀) (H.map f₁) := by
    apply biprod.hom_ext
    · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst, biprod.lift_fst_assoc, biprod.map_fst, ← H.map_comp]
    · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_snd, biprod.lift_snd_assoc, biprod.map_snd, ← H.map_comp]
  haveI : IsIso (H.map (biprod.map f₀ f₁) ≫ (H.mapBiprod L₀ L₁).hom) := by
    rw [hc]
    infer_instance
  change IsIso (H.map (biprod.map f₀ f₁))
  exact IsIso.of_isIso_comp_right _ (H.mapBiprod L₀ L₁).hom

/-- 同じ直和模型の射の像の擬同型性は、元の二本の射の像から分かる。 -/
theorem mappedBiprod_quasiIso_model (F : Complex A ⥤ Complex B) [F.Additive]
    {K₀ K₁ L₀ L₁ : Complex A} (f₀ : K₀ ⟶ L₀) (f₁ : K₁ ⟶ L₁)
    [QuasiIso (F.map f₀)] [QuasiIso (F.map f₁)] :
    QuasiIso (F.map (biprod.map f₀ f₁)) := by
  haveI := quasiIso_biprod_map_model (F.map f₀) (F.map f₁)
  have h : QuasiIso (F.map (biprod.map f₀ f₁) ≫ (F.mapBiprod L₀ L₁).hom) := by
    rw [mapBiprod_map_square]
    infer_instance
  exact (quasiIso_iff_comp_right _ _).mp h

/-- 同じ二本のK-flat複体の元の直和もK-flat。 -/
theorem complexKFlat_biprod_model (K L : Complex A) (hK : complexKFlat A K)
    (hL : complexKFlat A L) : complexKFlat A (K ⊞ L) := by
  intro Z hZ n
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ n).mpr
  let T := tensorRight Z
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) n
  have h₀ : IsZero (H.obj (T.obj K)) := (hK Z hZ n).isZero_homology
  have h₁ : IsZero (H.obj (T.obj L)) := (hL Z hZ n).isZero_homology
  have hz : IsZero (H.obj (T.obj K) ⊞ H.obj (T.obj L)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    rw [← biprod.total, h₀.eq_of_tgt (biprod.fst) 0, h₁.eq_of_tgt (biprod.snd) 0,
      zero_comp, zero_comp, zero_add]
  exact hz.of_iso (H.mapIso (T.mapBiprod K L) ≪≫ H.mapBiprod (T.obj K) (T.obj L))

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
