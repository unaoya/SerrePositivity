module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.ObjectProperty.ClosureShift
public import SerrePositivity.DifferentialGraded.Derived.Functor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import SerrePositivity.DifferentialGraded.Derived.Projective

public import SerrePositivity.DifferentialGraded.Derived.Basic

public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Logic.Small.Set

public import Mathlib.CategoryTheory.ObjectProperty.Small
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-!
# Perfect.Compact.Enhancement

## 概要
compact 性の閉性、Perf の本質的小性と小さい dg enhancementをまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## Compact（旧 SerrePositivity/DifferentialGraded/Perfect/Compact.lean） -/

/-! # u-small余積に関するdg導来加群のcompact性

加法圏でのcompact性を、余積への射が有限個の包含の像の和となる条件で表す。
余積の添字宇宙はuであり、主導来圏の対象宇宙をsmallと仮定しない。
-/

@[expose] public section Compact
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleCompact : ObjectProperty (DerivedModuleCategory A D) := fun X =>
  ∀ (J : Type u) (F : J → DerivedModuleCategory A D) (f : X ⟶ ∐ F),
    ∃ (t : Finset J) (g : ∀ j, X ⟶ F j), ∑ j ∈ t, g j ≫ Sigma.ι F j = f

/-- 代表加群は、任意のu-smallな主導来対象族に対してcompact。 -/
lemma moduleRepresentable_compact (x : D) :
    moduleCompact A D ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x))) := by
  classical
  intro J F f
  let R := fun j => moduleCanonicalProjectiveResolution A D (F j).as.obj
  let P := fun j => (R j).obj
  let e (j : J) : (moduleToDerived A D).obj (P j) ≅ F j :=
    moduleDerivedIso A D (R j).π (R j).quasiIso
  let s : Cofan (fun j => (moduleToDerived A D).obj (P j)) :=
    Cofan.mk (∐ F) (fun j => (e j).hom ≫ Sigma.ι F j)
  let k := moduleProjectiveDerivedCofanDesc A D P (fun j => (R j).projective) s
  let l : (∐ F) ⟶ (moduleToDerived A D).obj (∐ P) :=
    Sigma.desc (fun j => (e j).inv ≫ (moduleToDerived A D).map (Sigma.ι P j))
  have hk (j : J) : (moduleToDerived A D).map (Sigma.ι P j) ≫ k =
      (e j).hom ≫ Sigma.ι F j :=
    moduleProjectiveDerivedCofanDesc_fac A D P (fun j => (R j).projective) s j
  have hlk : l ≫ k = 𝟙 (∐ F) := by
    apply Sigma.hom_ext
    intro j
    simp only [l, Sigma.ι_comp_desc_assoc, hk, Category.assoc,
      Iso.inv_hom_id_assoc, Category.comp_id]
  obtain ⟨t, g, hg⟩ := moduleRepresentableDerivedCoproduct_rep A D x P (f ≫ l)
  refine ⟨t, fun j => g j ≫ (e j).hom, ?_⟩
  calc
    _ = ∑ j ∈ t, (g j ≫ (moduleToDerived A D).map (Sigma.ι P j)) ≫ k := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [Category.assoc, hk]
    _ = (∑ j ∈ t, g j ≫ (moduleToDerived A D).map (Sigma.ι P j)) ≫ k :=
      (sum_comp _ _ _).symm
    _ = f := by rw [hg, Category.assoc, hlk, Category.comp_id]

end SerrePositivity.DifferentialGraded
end

end Compact

/-! ## CompactComparison（旧 SerrePositivity/DifferentialGraded/Perfect/CompactComparison.lean） -/

/-! # compact性と標準Hom直和比較の全単射性 -/

@[expose] public section CompactComparison
universe u v

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def derivedPostcomposeLinearMap {X Y Z : DerivedModuleCategory A D} (g : Y ⟶ Z) :
    (X ⟶ Y) →ₗ[A] (X ⟶ Z) where
  toFun f := f ≫ g
  map_add' f h := Preadditive.add_comp _ _ _ f h g
  map_smul' a f := Linear.smul_comp _ _ _ a f g

def moduleCompactComparison {J : Type u} (X : DerivedModuleCategory A D)
    (F : J → DerivedModuleCategory A D) :
    DirectSum J (fun j => X ⟶ F j) →ₗ[A] (X ⟶ ∐ F) :=
  DirectSum.toModule A J _ (fun j => derivedPostcomposeLinearMap A D (Sigma.ι F j))

lemma moduleCompactComparison_lof {J : Type u} (X : DerivedModuleCategory A D)
    (F : J → DerivedModuleCategory A D) (j : J) (f : X ⟶ F j) :
    moduleCompactComparison A D X F (DirectSum.lof A J (fun j => X ⟶ F j) j f) =
      f ≫ Sigma.ι F j :=
  by
    change DirectSum.toModule A J _
      (fun j => derivedPostcomposeLinearMap A D (Sigma.ι F j))
        (DirectSum.lof A J (fun j => X ⟶ F j) j f) =
      (derivedPostcomposeLinearMap A D (Sigma.ι F j)) f
    exact DirectSum.toModule_lof A (M := fun i => X ⟶ F i)
      (φ := fun j => derivedPostcomposeLinearMap A D (Sigma.ι F j)) j f

lemma moduleCompactComparison_injective {J : Type u} (X : DerivedModuleCategory A D)
    (F : J → DerivedModuleCategory A D) :
    Function.Injective (moduleCompactComparison A D X F) := by
  classical
  intro a b hab
  apply DFinsupp.ext
  intro j
  let p : (∐ F) ⟶ F j := Sigma.desc (Pi.single j (𝟙 (F j)))
  have he : (derivedPostcomposeLinearMap A D p).comp (moduleCompactComparison A D X F) =
      DirectSum.component A J (fun i => X ⟶ F i) j := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro f
    change moduleCompactComparison A D X F (DirectSum.lof A J (fun i => X ⟶ F i) i f) ≫ p = _
    rw [moduleCompactComparison_lof, Category.assoc]
    change f ≫ (Sigma.ι F i ≫ p) = (DirectSum.of (fun i => X ⟶ F i) i f) j
    by_cases hij : i = j
    · subst i
      simp [p]
    · rw [DirectSum.of_eq_of_ne (β := fun i => X ⟶ F i) i j f (Ne.symm hij)]
      simp [p, hij]
  have ha := congrArg (fun k => k a) he
  have hb := congrArg (fun k => k b) he
  exact ha.symm.trans ((congrArg (fun k => k ≫ p) hab).trans hb)

lemma moduleCompact_iff_comparison_surjective (X : DerivedModuleCategory A D) :
    moduleCompact A D X ↔ ∀ (J : Type u) (F : J → DerivedModuleCategory A D),
      Function.Surjective (moduleCompactComparison A D X F) := by
  classical
  constructor
  · intro h J F f
    obtain ⟨t, g, hg⟩ := h J F f
    refine ⟨∑ j ∈ t, DirectSum.lof A J (fun j => X ⟶ F j) j (g j), ?_⟩
    simpa only [map_sum, moduleCompactComparison_lof] using hg
  · intro h J F f
    obtain ⟨a, ha⟩ := h J F f
    refine ⟨a.support, fun j => a j, ?_⟩
    have he := congrArg (moduleCompactComparison A D X F) (DirectSum.sum_support_of a)
    have hterm (j : J) : moduleCompactComparison A D X F
        (DirectSum.of (fun i => X ⟶ F i) j (a j)) = a j ≫ Sigma.ι F j :=
      moduleCompactComparison_lof A D X F j (a j)
    simpa only [map_sum, hterm, ha] using he

lemma moduleCompact_iff_comparison_bijective (X : DerivedModuleCategory A D) :
    moduleCompact A D X ↔ ∀ (J : Type u) (F : J → DerivedModuleCategory A D),
      Function.Bijective (moduleCompactComparison A D X F) := by
  rw [moduleCompact_iff_comparison_surjective]
  constructor
  · intro h J F
    exact ⟨moduleCompactComparison_injective A D X F, h J F⟩
  · intro h J F
    exact (h J F).2

def moduleCompactHomLinearEquiv {X : DerivedModuleCategory A D} (hX : moduleCompact A D X)
    {J : Type u} (F : J → DerivedModuleCategory A D) :
    DirectSum J (fun j => X ⟶ F j) ≃ₗ[A] (X ⟶ ∐ F) :=
  LinearEquiv.ofBijective (moduleCompactComparison A D X F)
    ((moduleCompact_iff_comparison_bijective A D X).mp hX J F)

end SerrePositivity.DifferentialGraded
end

end CompactComparison

/-! ## CompactRetracts（旧 SerrePositivity/DifferentialGraded/Perfect/CompactRetracts.lean） -/

/-! # compact dg導来対象のretract・同型閉性 -/

@[expose] public section CompactRetracts
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleCompact_of_retract {X Y : DerivedModuleCategory A D}
    (r : Retract X Y) (hY : moduleCompact A D Y) : moduleCompact A D X := by
  intro J F f
  obtain ⟨t, g, hg⟩ := hY J F (r.r ≫ f)
  refine ⟨t, fun j => r.i ≫ g j, ?_⟩
  calc
    _ = r.i ≫ ∑ j ∈ t, g j ≫ Sigma.ι F j := by
      rw [comp_sum]
      exact Finset.sum_congr rfl (fun j _ => Category.assoc _ _ _)
    _ = f := by rw [hg, ← Category.assoc, r.retract, Category.id_comp]

instance moduleCompactStableUnderRetracts : (moduleCompact A D).IsStableUnderRetracts where
  of_retract := moduleCompact_of_retract A D

instance moduleCompactClosedUnderIso : (moduleCompact A D).IsClosedUnderIsomorphisms :=
  inferInstance

lemma moduleCompact_of_isZero {X : DerivedModuleCategory A D} (hX : IsZero X) :
    moduleCompact A D X := by
  intro J F f
  refine ⟨∅, fun _ => 0, ?_⟩
  rw [Finset.sum_empty]
  exact hX.eq_of_src _ _

end SerrePositivity.DifferentialGraded
end

end CompactRetracts

/-! ## CompactShift（旧 SerrePositivity/DifferentialGraded/Perfect/CompactShift.lean） -/

/-! # compact dg導来対象の整数shift閉性 -/

@[expose] public section CompactShift
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleCompact_equivalence (E : DerivedModuleCategory A D ≌ DerivedModuleCategory A D)
    [E.functor.Additive] {X : DerivedModuleCategory A D} (hX : moduleCompact A D X) :
    moduleCompact A D (E.functor.obj X) := by
  classical
  intro J F f
  let e := PreservesCoproduct.iso E.inverse F
  let b := E.toAdjunction.homEquiv X (∐ F) f
  obtain ⟨t, g, hg⟩ := hX J (fun j => E.inverse.obj (F j)) (b ≫ e.hom)
  refine ⟨t, fun j => (E.toAdjunction.homEquiv X (F j)).symm (g j), ?_⟩
  apply (E.toAdjunction.homAddEquiv X (∐ F)).injective
  calc
    _ = ∑ j ∈ t, g j ≫ E.inverse.map (Sigma.ι F j) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact (E.toAdjunction.homEquiv_naturality_right _ _).trans
        (by rw [Equiv.apply_symm_apply])
    _ = (∑ j ∈ t, g j ≫ Sigma.ι (fun j => E.inverse.obj (F j)) j) ≫ e.inv := by
      rw [sum_comp]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Category.assoc, e, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]
    _ = _ := by
      rw [hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rfl

lemma moduleCompact_shift {X : DerivedModuleCategory A D} (hX : moduleCompact A D X) (n : ℤ) :
    moduleCompact A D (X⟦n⟧) := by
  let E := shiftEquiv (DerivedModuleCategory A D) n
  have : E.functor.Additive := by
    change (shiftFunctor (DerivedModuleCategory A D) n).Additive
    infer_instance
  exact moduleCompact_equivalence A D E hX

instance moduleCompactStableUnderShift : (moduleCompact A D).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun _ hX => moduleCompact_shift A D hX n⟩

end SerrePositivity.DifferentialGraded
end

end CompactShift

/-! ## CompactTriangles（旧 SerrePositivity/DifferentialGraded/Perfect/CompactTriangles.lean） -/

/-! # compact dg導来対象の三角閉性 -/

@[expose] public section CompactTriangles
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive Pretriangulated
open scoped ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleCompactRange_ι {J : Type u} {X : DerivedModuleCategory A D}
    (F : J → DerivedModuleCategory A D) (j : J) (f : X ⟶ F j) :
    f ≫ Sigma.ι F j ∈ (moduleCompactComparison A D X F).range := by
  classical
  exact ⟨DirectSum.lof A J (fun j => X ⟶ F j) j f,
    moduleCompactComparison_lof A D X F j f⟩

lemma moduleCompactRange_precompose {J : Type u} {X Y : DerivedModuleCategory A D}
    (hY : moduleCompact A D Y) (F : J → DerivedModuleCategory A D)
    (f : X ⟶ Y) (g : Y ⟶ ∐ F) :
    f ≫ g ∈ (moduleCompactComparison A D X F).range := by
  obtain ⟨t, a, ha⟩ := hY J F g
  rw [← ha, comp_sum]
  apply Submodule.sum_mem
  intro j _
  simpa only [Category.assoc] using moduleCompactRange_ι A D F j (f ≫ a j)

lemma moduleCompactRange_finiteProjection {J : Type u} {X : DerivedModuleCategory A D}
    (F : J → DerivedModuleCategory A D) (t : Finset J) (f : X ⟶ ∐ F) :
    f ≫ moduleDerivedCoproductFiniteProjection A D F t ∈
      (moduleCompactComparison A D X F).range := by
  rw [moduleDerivedCoproductFiniteProjection, comp_sum]
  apply Submodule.sum_mem
  intro j _
  simpa only [Category.assoc] using
    moduleCompactRange_ι A D F j (f ≫ moduleDerivedCoproductProjection A D F j)

lemma moduleCompact_triangle_obj₃ (T : Triangle (DerivedModuleCategory A D))
    (hT : T ∈ distTriang (DerivedModuleCategory A D))
    (h₁ : moduleCompact A D T.obj₁) (h₂ : moduleCompact A D T.obj₂) :
    moduleCompact A D T.obj₃ := by
  rw [moduleCompact_iff_comparison_surjective]
  intro J F f
  obtain ⟨t, g, hg⟩ := h₂ J F (T.mor₂ ≫ f)
  let p := moduleDerivedCoproductFiniteProjection A D F t
  let q := 𝟙 (∐ F) - p
  have hf : T.mor₂ ≫ (f ≫ q) = 0 := by
    rw [← Category.assoc, ← hg, sum_comp]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Category.assoc]
    change g j ≫ (Sigma.ι F j ≫
      (𝟙 (∐ F) - moduleDerivedCoproductFiniteProjection A D F t)) = 0
    rw [moduleDerivedCoproductComplement_mem A D F t j hj, comp_zero]
  obtain ⟨a, ha⟩ := Triangle.yoneda_exact₃ T hT (f ≫ q) hf
  have hsplit : f = f ≫ p + T.mor₃ ≫ a := by
    rw [← ha]
    dsimp only [q]
    rw [comp_sub, Category.comp_id]
    abel
  change f ∈ (moduleCompactComparison A D T.obj₃ F).range
  rw [hsplit]
  exact Submodule.add_mem _ (moduleCompactRange_finiteProjection A D F t f)
    (moduleCompactRange_precompose A D (moduleCompact_shift A D h₁ 1) F T.mor₃ a)

instance moduleCompactTriangulatedClosed₃ : (moduleCompact A D).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk' (moduleCompact_triangle_obj₃ A D)

instance moduleCompactTriangulatedClosed₂ : (moduleCompact A D).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

instance moduleCompactContainsZero : (moduleCompact A D).ContainsZero :=
  ⟨⟨0, isZero_zero _, moduleCompact_of_isZero A D (isZero_zero _)⟩⟩

instance moduleCompactIsTriangulated : (moduleCompact A D).IsTriangulated := by
  constructor

end SerrePositivity.DifferentialGraded
end

end CompactTriangles

/-! ## Enhancement（旧 SerrePositivity/DifferentialGraded/Perfect/Enhancement.lean） -/

/-! # 射影的perfect dg加群による主Perfのenhancement

対象は実際の右dg加群、Homは元の全次数Hom endである。
小さい代表系への制限は別に証明し、この対象型全体をsmallと仮定しない。
-/

@[expose] public section Enhancement
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 実際の右dg加群が射影的で、その主導来像が指定生成集合SのPerfに入るという性質。 -/
def modulePerfectProjectiveOver (S : Set D) (M : RightModule A D) : Prop :=
  moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) M) ∧
    modulePerfectOver A D S ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) M))

/-- 射影的perfect右dg加群の充満dg部分圏。全対象のsmall性は仮定しない。 -/
abbrev PerfectDGModuleOver (S : Set D) :=
  DGFullSubcategory (RightModule A D) (modulePerfectProjectiveOver A D S)

/-- 全代表加群から生成する射影的perfect dg部分圏。 -/
abbrev PerfectDGModule := PerfectDGModuleOver A D Set.univ

/-- 射影的perfect加群から全右dg加群への全Homを保つ包含。 -/
def perfectDGModuleInclusion (S : Set D) :
    DGFunctor A (PerfectDGModuleOver A D S) (RightModule A D) :=
  dgFullSubcategoryInclusion A (RightModule A D) (modulePerfectProjectiveOver A D S)

/-- 射影的perfect加群のH⁰包含は充満。充満dg部分圏の一般補題を適用する。 -/
instance perfectDGModuleInclusionHomotopyFull (S : Set D) :
    (perfectDGModuleInclusion A D S).onHomotopy.Full := by
  dsimp [perfectDGModuleInclusion]
  infer_instance

/-- 射影的perfect加群のH⁰包含は忠実。同一のHomと境界関係を使う。 -/
instance perfectDGModuleInclusionHomotopyFaithful (S : Set D) :
    (perfectDGModuleInclusion A D S).onHomotopy.Faithful := by
  dsimp [perfectDGModuleInclusion]
  infer_instance

/-- 射影的perfect dg部分圏の実際のH⁰。 -/
abbrev PerfectDGHomotopyCategoryOver (S : Set D) := HomotopyCategory A (PerfectDGModuleOver A D S)

/-- H⁰包含を既存K(D)から主導来圏への関手と合成した比較。 -/
def perfectDGModuleToDerived (S : Set D) :
    PerfectDGHomotopyCategoryOver A D S ⥤ DerivedModuleCategory A D :=
  (perfectDGModuleInclusion A D S).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D

/-- 比較の像は指定Perfに入る。Qとの自然同型で対象に保持した証拠を運ぶ。 -/
lemma perfectDGModuleToDerived_obj_perfect (S : Set D) (X : PerfectDGHomotopyCategoryOver A D S) :
    modulePerfectOver A D S ((perfectDGModuleToDerived A D S).obj X) := by
  let M : PerfectDGModuleOver A D S := ForgetEnrichment.to (Complex A) X.as
  exact (modulePerfectOver A D S).prop_of_iso
    ((moduleToHomotopyDerivedIso A D).app (ForgetEnrichment.of (Complex A) M.val)).symm M.property.2

/-- 主導来比較は充満。始域の射影性による局所化Hom計算とH⁰包含の充満性を使う。 -/
instance perfectDGModuleToDerivedFull (S : Set D) : (perfectDGModuleToDerived A D S).Full where
  map_surjective {X Y} f := by
    let M : PerfectDGModuleOver A D S := ForgetEnrichment.to (Complex A) X.as
    let N : ModuleCategory A D := ForgetEnrichment.of (Complex A) M.val
    obtain ⟨g, hg⟩ := (moduleProjectiveLocalization_map_bijective A D
      (P := N) M.property.1 ((perfectDGModuleInclusion A D S).onHomotopy.obj Y)).2 f
    obtain ⟨h, hh⟩ := (perfectDGModuleInclusion A D S).onHomotopy.map_surjective g
    refine ⟨h, ?_⟩
    change (moduleHomotopyToDerivedClosed A D).map
      ((perfectDGModuleInclusion A D S).onHomotopy.map h) = f
    rw [hh]
    exact hg

/-- 主導来比較は忠実。射影対象からの局所化Hom写像の単射性を使う。 -/
instance perfectDGModuleToDerivedFaithful (S : Set D) :
    (perfectDGModuleToDerived A D S).Faithful where
  map_injective {X Y} f g h := by
    let M : PerfectDGModuleOver A D S := ForgetEnrichment.to (Complex A) X.as
    let N : ModuleCategory A D := ForgetEnrichment.of (Complex A) M.val
    apply (perfectDGModuleInclusion A D S).onHomotopy.map_injective
    exact (moduleProjectiveLocalization_map_bijective A D
      (P := N) M.property.1 ((perfectDGModuleInclusion A D S).onHomotopy.obj Y)).1 h

/-- 主導来比較を、その全本質像を含む指定Perfへ制限する。 -/
def perfectDGModuleToPerfect (S : Set D) :
    PerfectDGHomotopyCategoryOver A D S ⥤ PerfectModuleCategoryOver A D S :=
  (modulePerfectOver A D S).lift (perfectDGModuleToDerived A D S)
    (perfectDGModuleToDerived_obj_perfect A D S)

/-- Perfへの制限も充満。充満部分圏への持ち上げの性質を用いる。 -/
instance perfectDGModuleToPerfectFull (S : Set D) : (perfectDGModuleToPerfect A D S).Full := by
  dsimp [perfectDGModuleToPerfect]
  infer_instance

/-- Perfへの制限も忠実。主導来比較の忠実性を継承する。 -/
instance perfectDGModuleToPerfectFaithful (S : Set D) :
    (perfectDGModuleToPerfect A D S).Faithful := by
  dsimp [perfectDGModuleToPerfect]
  infer_instance

/-- 任意のPerf対象を標準射影解像度で表し、本質的全射性を得る。smallな代表選択は別工程である。 -/
instance perfectDGModuleToPerfectEssSurj (S : Set D) :
    (perfectDGModuleToPerfect A D S).EssSurj where
  mem_essImage X := by
    let R := moduleCanonicalProjectiveResolution A D X.obj.as.obj
    let e : (moduleToDerived A D).obj R.obj ≅ X.obj := moduleDerivedIso A D R.π R.quasiIso
    let M : PerfectDGModuleOver A D S :=
      ⟨ForgetEnrichment.to (Complex A) R.obj, R.projective,
        (modulePerfectOver A D S).prop_of_iso e.symm X.property⟩
    refine ⟨(toHomotopy A (PerfectDGModuleOver A D S)).obj
      (ForgetEnrichment.of (Complex A) M), ⟨(modulePerfectOver A D S).isoMk ?_⟩⟩
    exact (moduleToHomotopyDerivedIso A D).app R.obj ≪≫ e

/-- 完全忠実性と射影解像度による本質的全射性から比較は同値となる。 -/
instance perfectDGModuleToPerfectIsEquivalence (S : Set D) :
    (perfectDGModuleToPerfect A D S).IsEquivalence where

/-- 射影的perfect加群のH⁰と主Perfの同値。shift・三角構造の比較は別に検証する。 -/
def perfectDGModuleHomotopyEquivalence (S : Set D) :
    PerfectDGHomotopyCategoryOver A D S ≌ PerfectModuleCategoryOver A D S :=
  (perfectDGModuleToPerfect A D S).asEquivalence

end SerrePositivity.DifferentialGraded
end

end Enhancement

/-! ## EnhancementLinear（旧 SerrePositivity/DifferentialGraded/Perfect/EnhancementLinear.lean） -/

/-! # 射影的perfect加群によるH⁰比較の線形性 -/

@[expose] public section EnhancementLinear
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 主導来比較は加法的。H⁰包含と局所化比較の合成として継承する。 -/
instance perfectDGModuleToDerivedAdditive (S : Set D) :
    (perfectDGModuleToDerived A D S).Additive := by
  dsimp [perfectDGModuleToDerived]
  infer_instance

/-- 主導来比較はA線形。既存Hom endの線形性とK(D)比較を使用する。 -/
instance perfectDGModuleToDerivedLinear (S : Set D) :
    (perfectDGModuleToDerived A D S).Linear A := by
  dsimp [perfectDGModuleToDerived]
  infer_instance

/-- Perfへの持ち上げは主導来比較の加法性を保つ。 -/
instance perfectDGModuleToPerfectAdditive (S : Set D) :
    (perfectDGModuleToPerfect A D S).Additive := by
  dsimp [perfectDGModuleToPerfect]
  infer_instance

/-- Perfへの持ち上げはA線形。充満部分圏の射の外延性で確認する。 -/
instance perfectDGModuleToPerfectLinear (S : Set D) :
    (perfectDGModuleToPerfect A D S).Linear A where
  map_smul f a := (modulePerfectOver A D S).hom_ext
    ((perfectDGModuleToDerived A D S).map_smul a f)

/-- 選択した同値の順関手は加法的比較そのものである。 -/
instance perfectDGModuleHomotopyEquivalenceFunctorAdditive (S : Set D) :
    (perfectDGModuleHomotopyEquivalence A D S).functor.Additive := by
  change (perfectDGModuleToPerfect A D S).Additive
  infer_instance

/-- 選択した同値の順関手はA線形。逆関手の線形性もMathlibの同値APIから得る。 -/
instance perfectDGModuleHomotopyEquivalenceFunctorLinear (S : Set D) :
    (perfectDGModuleHomotopyEquivalence A D S).functor.Linear A := by
  change (perfectDGModuleToPerfect A D S).Linear A
  infer_instance

/-- Perfへの比較と主導来包含の合成を、元の主導来比較と同定する自然同型。 -/
def perfectDGModuleToPerfectCompInclusion (S : Set D) :
    perfectDGModuleToPerfect A D S ⋙ perfectModuleInclusion A D S ≅
      perfectDGModuleToDerived A D S :=
  (modulePerfectOver A D S).liftCompιIso _ _

end SerrePositivity.DifferentialGraded
end

end EnhancementLinear

/-! ## PerfectCompact（旧 SerrePositivity/DifferentialGraded/Perfect/PerfectCompact.lean） -/

/-! # 有限cellとそのretractのcompact性 -/

@[expose] public section PerfectCompact
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleCompact_derivedShift {M : ModuleCategory A D}
    (hM : moduleCompact A D ((moduleToDerived A D).obj M)) (n : ℤ) :
    moduleCompact A D ((moduleToDerived A D).obj (M⟦n⟧)) :=
  (moduleCompact A D).prop_of_iso (((moduleToDerived A D).commShiftIso n).app M).symm
    (moduleCompact_shift A D hM n)

lemma moduleCompact_derivedBiprod {M N : ModuleCategory A D}
    (hM : moduleCompact A D ((moduleToDerived A D).obj M))
    (hN : moduleCompact A D ((moduleToDerived A D).obj N)) :
    moduleCompact A D ((moduleToDerived A D).obj (moduleBiprod A D M N)) := by
  rw [moduleCompact_iff_comparison_surjective]
  intro J F f
  have ht := congrArg ((moduleToDerived A D).map) (moduleBinaryBicone_total A D M N)
  change (moduleToDerived A D).map
    (moduleBiprodFst A D M N ≫ moduleBiprodInl A D M N +
      moduleBiprodSnd A D M N ≫ moduleBiprodInr A D M N) =
    (moduleToDerived A D).map (𝟙 (moduleBiprod A D M N)) at ht
  simp only [Functor.map_add, Functor.map_comp] at ht
  rw [(moduleToDerived A D).map_id] at ht
  have hf : f =
      (moduleToDerived A D).map (moduleBiprodFst A D M N) ≫
        ((moduleToDerived A D).map (moduleBiprodInl A D M N) ≫ f) +
      (moduleToDerived A D).map (moduleBiprodSnd A D M N) ≫
        ((moduleToDerived A D).map (moduleBiprodInr A D M N) ≫ f) := by
    rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, ht, Category.id_comp]
  change f ∈ (moduleCompactComparison A D _ F).range
  rw [hf]
  exact Submodule.add_mem _
    (moduleCompactRange_precompose A D hM F _ _)
    (moduleCompactRange_precompose A D hN F _ _)

lemma moduleCompact_derivedCone {M N : ModuleCategory A D}
    (hM : moduleCompact A D ((moduleToDerived A D).obj M))
    (hN : moduleCompact A D ((moduleToDerived A D).obj N)) (f : M ⟶ N) :
    moduleCompact A D ((moduleToDerived A D).obj (moduleCone A D f)) :=
  moduleCompact_triangle_obj₃ A D (moduleDerivedConeTriangle A D f)
    (moduleDerivedConeTriangle_distinguished A D f) hM hN

lemma ModuleFiniteCellCode.compact {S : Set D} {M : ModuleCategory A D}
    (c : ModuleFiniteCellCode A D S M) : moduleCompact A D ((moduleToDerived A D).obj M) := by
  induction c with
  | zero =>
    exact moduleCompact_of_isZero A D
      ((moduleToDerived A D).map_isZero (moduleZero_isZero A D))
  | generator x hx => exact moduleRepresentable_compact A D x
  | shift s c ih => exact moduleCompact_derivedShift A D ih s
  | sum c d ihc ihd => exact moduleCompact_derivedBiprod A D ihc ihd
  | cone c d f ihc ihd => exact moduleCompact_derivedCone A D ihc ihd f
  | iso c e ih => exact (moduleCompact A D).prop_of_iso ((moduleToDerived A D).mapIso e) ih

lemma moduleFiniteCellOver_compact {S : Set D} {M : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) : moduleCompact A D ((moduleToDerived A D).obj M) := by
  obtain ⟨c⟩ := hM
  exact c.compact A D

lemma moduleFiniteCell_compact {M : ModuleCategory A D} (hM : moduleFiniteCell A D M) :
    moduleCompact A D ((moduleToDerived A D).obj M) := moduleFiniteCellOver_compact A D hM

lemma modulePerfectOver_compact {S : Set D} {X : DerivedModuleCategory A D}
    (hX : modulePerfectOver A D S X) : moduleCompact A D X := by
  obtain ⟨M, hM, ⟨r⟩⟩ := (modulePerfectOver_iff A D S X).mp hX
  exact moduleCompact_of_retract A D r (moduleFiniteCellOver_compact A D hM)

lemma modulePerfect_compact {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    moduleCompact A D X := modulePerfectOver_compact A D hX

end SerrePositivity.DifferentialGraded
end

end PerfectCompact

/-! ## Generators（旧 SerrePositivity/DifferentialGraded/Perfect/Generators.lean） -/

/-! # 代表加群の整数shiftによる主導来圏のcompact生成性 -/

@[expose] public section Generators
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleEvaluationShiftHomologyIso (x : D) (N : ModuleCategory A D) (n : ℤ) :
    ((moduleEvaluation A D x).obj (N⟦n⟧)).homology 0 ≅
      ((moduleEvaluation A D x).obj N).homology n :=
  HomologicalComplex.homologyMapIso (((moduleEvaluation A D x).commShiftIso n).app N) 0 ≪≫
    (CochainComplex.ShiftSequence.shiftIso (ModuleCat A) n 0 n (by omega)).app
      ((moduleEvaluation A D x).obj N)

lemma moduleRepresentables_detect_zero (X : DerivedModuleCategory A D) :
    IsZero X ↔ ∀ (x : D) (n : ℤ), Subsingleton
      ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ X⟦n⟧) := by
  constructor
  · intro hX x n
    exact ⟨fun f g => ((shiftFunctor (DerivedModuleCategory A D) n).map_isZero hX).eq_of_tgt f g⟩
  · intro hX
    obtain ⟨⟨N⟩⟩ := X
    apply moduleToDerived_isZero_of_acyclic A D
    intro x n
    have : Subsingleton
        ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
          (moduleToDerived A D).obj (N⟦n⟧)) :=
      ⟨fun f g =>
        (Iso.homCongr (Iso.refl _) (((moduleToDerived A D).commShiftIso n).app N)).injective
          (@Subsingleton.elim _ (hX x n) _ _)⟩
    have : Subsingleton (((moduleEvaluation A D x).obj (N⟦n⟧)).homology 0) :=
      (moduleRepresentableDerivedHomologyEquiv A D x (N⟦n⟧)).symm.injective.subsingleton
    have : Subsingleton (((moduleEvaluation A D x).obj N).homology n) :=
      (moduleEvaluationShiftHomologyIso A D x N n).toLinearEquiv.symm.injective.subsingleton
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (ModuleCat.isZero_iff_subsingleton.mpr inferInstance)

lemma moduleRepresentableShifts_detect_zero (X : DerivedModuleCategory A D) :
    IsZero X ↔ ∀ (x : D) (n : ℤ), Subsingleton
      (((moduleToDerived A D).obj
        (ForgetEnrichment.of (Complex A) (representable A x)))⟦n⟧ ⟶ X) := by
  constructor
  · intro hX x n
    exact ⟨fun f g => hX.eq_of_tgt f g⟩
  · intro hX
    apply (moduleRepresentables_detect_zero A D X).mpr
    intro x n
    let e := (shiftEquiv' (DerivedModuleCategory A D) (-n) n
      (neg_add_cancel n)).toAdjunction.homEquiv
      ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x))) X
    exact ⟨fun f g => e.symm.injective (@Subsingleton.elim _ (hX x (-n)) _ _)⟩

def moduleCompactGenerators (p : D × ℤ) : DerivedModuleCategory A D :=
  ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A p.1)))⟦p.2⟧

lemma moduleCompactGenerators_small : Small.{u} (Set.range (moduleCompactGenerators A D)) := by
  infer_instance

lemma moduleCompactGenerators_compact (p : D × ℤ) :
    moduleCompact A D (moduleCompactGenerators A D p) :=
  moduleCompact_shift A D (moduleRepresentable_compact A D p.1) p.2

lemma moduleCompactGenerators_detect_zero (X : DerivedModuleCategory A D) :
    IsZero X ↔ ∀ p : D × ℤ, Subsingleton (moduleCompactGenerators A D p ⟶ X) := by
  rw [moduleRepresentableShifts_detect_zero]
  constructor
  · intro h p
    exact h p.1 p.2
  · intro h x n
    exact h (x, n)

end SerrePositivity.DifferentialGraded
end

end Generators

/-! ## EssentiallySmall（旧 SerrePositivity/DifferentialGraded/Perfect/EssentiallySmall.lean） -/

/-! # 主導来圏内のPerfの本質的小性

小さい有限cell代表族の関手像とretract閉包を使う。全加群圏や導来圏の対象型をsmallとはしない。
-/

@[expose] public section EssentiallySmall
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 有限cellの小さい段階別代表が全finite cellを同型まで被覆する。 -/
instance moduleFiniteCellOverEssentiallySmall (S : Set D) :
    ObjectProperty.EssentiallySmall.{u} (moduleFiniteCellOver A D S) where
  exists_small_le' := by
    refine ⟨ObjectProperty.ofObj (moduleFiniteCellStageObject A D S), inferInstance, ?_⟩
    intro M hM
    obtain ⟨i, ⟨e⟩⟩ := moduleFiniteCellOver_exists_stage A D hM
    exact ⟨_, ⟨i⟩, ⟨e.symm⟩⟩

/-- finite cellの主導来像は、固定版Mathlibの関手像の定理により本質的にu-small。 -/
instance derivedFiniteCellOverEssentiallySmall (S : Set D) :
    ObjectProperty.EssentiallySmall.{u} (derivedFiniteCellOver A D S) := by
  dsimp [derivedFiniteCellOver]
  infer_instance

/-- 主導来圏の局所小性とretract閉包の一般定理からPerfの本質的小性を得る。 -/
instance modulePerfectOverEssentiallySmall (S : Set D) :
    ObjectProperty.EssentiallySmall.{u} (modulePerfectOver A D S) := by
  dsimp [modulePerfectOver]
  infer_instance

/-- Perfの充満部分圏はu-smallな圏と同値である。対象型そのもののsmall性とは区別する。 -/
instance perfectModuleCategoryOverEssentiallySmall (S : Set D) :
    EssentiallySmall.{u} (PerfectModuleCategoryOver A D S) := inferInstance

/-- 実際の主導来対象からなる小さい代表部分族を、Perf内に選択できる。 -/
lemma modulePerfectOver_exists_small_representatives (S : Set D) :
    ∃ (P : ObjectProperty (DerivedModuleCategory A D)) (_ : ObjectProperty.Small.{u} P),
      P ≤ modulePerfectOver A D S ∧ modulePerfectOver A D S ≤ P.isoClosure :=
  ObjectProperty.EssentiallySmall.exists_small_le (modulePerfectOver A D S)

end SerrePositivity.DifferentialGraded
end

end EssentiallySmall

/-! ## SmallEnhancement（旧 SerrePositivity/DifferentialGraded/Perfect/SmallEnhancement.lean） -/

/-! # 小さい射影的perfect dg代表系

Perfの小さい通常モデルの各対象を、構成済みH⁰同値の逆関手で実際の射影的dg加群へ戻す。
その像の充満dg部分圏を取るので、全次数Hom endと微分を保持する。
-/

@[expose] public section SmallEnhancement
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- Perfの小さいモデルから、実際の射影的perfect dg加群の代表を選ぶ。 -/
def perfectDGModuleRepresentative (S : Set D)
    (i : SmallModel.{u} (PerfectModuleCategoryOver A D S)) : PerfectDGModuleOver A D S :=
  ForgetEnrichment.to (Complex A)
    (((perfectDGModuleHomotopyEquivalence A D S).inverse.obj
      ((equivSmallModel (PerfectModuleCategoryOver A D S)).inverse.obj i)).as)

/-- 小さい添字族で選んだ射影的代表の像による充満dg部分圏。 -/
abbrev SmallPerfectDGModuleOver (S : Set D) :=
  DGFullSubcategory (PerfectDGModuleOver A D S) (Set.range (perfectDGModuleRepresentative A D S))

/-- 小さい代表系の豊穣構造。入れ子の充満部分圏に対する既存構造を明示的に公開する。 -/
instance smallPerfectDGModuleEnrichment (S : Set D) :
    DGCategory A (SmallPerfectDGModuleOver A D S) :=
  dgFullSubcategoryEnrichment A (PerfectDGModuleOver A D S)
    (Set.range (perfectDGModuleRepresentative A D S))

/-- 代表の像は小さい。全ての射影的perfect加群の対象型をsmallとは仮定しない。 -/
instance smallPerfectDGModuleOverSmall (S : Set D) : Small.{u} (SmallPerfectDGModuleOver A D S) :=
  small_range (perfectDGModuleRepresentative A D S)

/-- 小さい代表dg圏から、全射影的perfect dg加群への包含。 -/
def smallPerfectDGModuleInclusion (S : Set D) :
    DGFunctor A (SmallPerfectDGModuleOver A D S) (PerfectDGModuleOver A D S) :=
  dgFullSubcategoryInclusion A _ (Set.range (perfectDGModuleRepresentative A D S))

/-- 小さい代表のH⁰包含は充満。全Homを制限したことから従う。 -/
instance smallPerfectDGModuleInclusionHomotopyFull (S : Set D) :
    (smallPerfectDGModuleInclusion A D S).onHomotopy.Full := by
  dsimp [smallPerfectDGModuleInclusion]
  infer_instance

/-- 小さい代表のH⁰包含は忠実。同じHom複体上の境界を使う。 -/
instance smallPerfectDGModuleInclusionHomotopyFaithful (S : Set D) :
    (smallPerfectDGModuleInclusion A D S).onHomotopy.Faithful := by
  dsimp [smallPerfectDGModuleInclusion]
  infer_instance

/-- 小さいdg代表系のH⁰から主Perfへの比較。 -/
def smallPerfectDGModuleToPerfect (S : Set D) :
    HomotopyCategory A (SmallPerfectDGModuleOver A D S) ⥤ PerfectModuleCategoryOver A D S :=
  (smallPerfectDGModuleInclusion A D S).onHomotopy ⋙ perfectDGModuleToPerfect A D S

/-- 小さい代表比較は充満。二つの充満比較の合成である。 -/
instance smallPerfectDGModuleToPerfectFull (S : Set D) :
    (smallPerfectDGModuleToPerfect A D S).Full := by
  dsimp [smallPerfectDGModuleToPerfect]
  infer_instance

/-- 小さい代表比較は忠実。全Homの包含と射影的局所化計算を継承する。 -/
instance smallPerfectDGModuleToPerfectFaithful (S : Set D) :
    (smallPerfectDGModuleToPerfect A D S).Faithful := by
  dsimp [smallPerfectDGModuleToPerfect]
  infer_instance

/-- 各小さい添字に対応する、実際の小さいdg部分圏の対象。 -/
def smallPerfectDGModuleObject (S : Set D)
    (i : SmallModel.{u} (PerfectModuleCategoryOver A D S)) : SmallPerfectDGModuleOver A D S :=
  ⟨perfectDGModuleRepresentative A D S i, ⟨i, rfl⟩⟩

/-- 選択した代表のH⁰比較は、元のPerf同値の逆関手で選んだ対象へ戻る。 -/
lemma smallPerfectDGModuleObject_comparison (S : Set D)
    (i : SmallModel.{u} (PerfectModuleCategoryOver A D S)) :
    (smallPerfectDGModuleToPerfect A D S).obj
      ((toHomotopy A (SmallPerfectDGModuleOver A D S)).obj
        (ForgetEnrichment.of (Complex A) (smallPerfectDGModuleObject A D S i))) =
    (perfectDGModuleHomotopyEquivalence A D S).functor.obj
      ((perfectDGModuleHomotopyEquivalence A D S).inverse.obj
        ((equivSmallModel (PerfectModuleCategoryOver A D S)).inverse.obj i)) := rfl

/-- 任意のPerf対象は選択した小さい射影的代表のH⁰像と同型である。 -/
instance smallPerfectDGModuleToPerfectEssSurj (S : Set D) :
    (smallPerfectDGModuleToPerfect A D S).EssSurj where
  mem_essImage X := by
    let e := equivSmallModel.{u} (PerfectModuleCategoryOver A D S)
    let i := e.functor.obj X
    refine ⟨(toHomotopy A (SmallPerfectDGModuleOver A D S)).obj
      (ForgetEnrichment.of (Complex A) (smallPerfectDGModuleObject A D S i)), ⟨?_⟩⟩
    rw [smallPerfectDGModuleObject_comparison]
    exact (perfectDGModuleHomotopyEquivalence A D S).counitIso.app (e.inverse.obj i) ≪≫
      (e.unitIso.app X).symm

/-- 小さいdg代表系のH⁰と主Perfの比較は同値となる。 -/
instance smallPerfectDGModuleToPerfectIsEquivalence (S : Set D) :
    (smallPerfectDGModuleToPerfect A D S).IsEquivalence where

/-- 小さいdg enhancementのH⁰による主Perfの同値表示。 -/
def smallPerfectDGModuleHomotopyEquivalence (S : Set D) :
    HomotopyCategory A (SmallPerfectDGModuleOver A D S) ≌ PerfectModuleCategoryOver A D S :=
  (smallPerfectDGModuleToPerfect A D S).asEquivalence

/-- 小さい代表系からの比較もA線形。全Hom包含と既存線形比較の合成から得る。 -/
instance smallPerfectDGModuleToPerfectLinear (S : Set D) :
    (smallPerfectDGModuleToPerfect A D S).Linear A := by
  dsimp [smallPerfectDGModuleToPerfect]
  infer_instance

/-- 小さい代表比較の加法性は、包含と主Perf比較の合成から従う。 -/
instance smallPerfectDGModuleToPerfectAdditive (S : Set D) :
    (smallPerfectDGModuleToPerfect A D S).Additive := by
  dsimp [smallPerfectDGModuleToPerfect]
  infer_instance

/-- 小さい代表のH⁰包含は本質的全射。主Perfでの比較同型を完全忠実関手で引き戻す。 -/
instance smallPerfectDGModuleInclusionHomotopyEssSurj (S : Set D) :
    (smallPerfectDGModuleInclusion A D S).onHomotopy.EssSurj where
  mem_essImage X := by
    obtain ⟨Y, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
      (smallPerfectDGModuleToPerfect A D S) ((perfectDGModuleToPerfect A D S).obj X)
    exact ⟨Y, ⟨(perfectDGModuleToPerfect A D S).preimageIso e⟩⟩

/-- 小さい代表のdg包含は準同値。各Homは恒等射で、H⁰は本質的全射である。 -/
lemma smallPerfectDGModuleInclusion_quasiEquivalence (S : Set D) :
    QuasiEquivalence (smallPerfectDGModuleInclusion A D S) := by
  refine ⟨?_, inferInstance⟩
  intro X Y
  change QuasiIso (𝟙 _)
  infer_instance

/-- 小さいenhancementのH⁰同値の順関手はA線形である。 -/
instance smallPerfectDGModuleHomotopyEquivalenceFunctorLinear (S : Set D) :
    (smallPerfectDGModuleHomotopyEquivalence A D S).functor.Linear A := by
  change (smallPerfectDGModuleToPerfect A D S).Linear A
  infer_instance

/-- 小さいenhancementのH⁰同値の順関手は加法的で、逆関手にも加法性が移る。 -/
instance smallPerfectDGModuleHomotopyEquivalenceFunctorAdditive (S : Set D) :
    (smallPerfectDGModuleHomotopyEquivalence A D S).functor.Additive := by
  change (smallPerfectDGModuleToPerfect A D S).Additive
  infer_instance

end SerrePositivity.DifferentialGraded
end

end SmallEnhancement

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.2.4.2" (partial := component) "仮定：可換環上の小さい dg 圏と全通常導来加群（Lean が強い：この dg 導来模型の場合）。結論：通常の三角圏の compact 性と perfect 性の同値、代表加群のシフトの compact 性と零対象の検出を示す（HA の compact・perfect と生成の通常の部分に一致）。∞ filtered 余極限による compact 性と環スペクトルへの比較は含まれない。"] _root_.SerrePositivity.DifferentialGraded.moduleCompactGenerators_compact
attribute [cite HA "7.2.4.2" (partial := component) "仮定：可換環上の小さい dg 圏と全通常導来加群（Lean が強い：この dg 導来模型の場合）。結論：通常の三角圏の compact 性と perfect 性の同値、代表加群のシフトの compact 性と零対象の検出を示す（HA の compact・perfect と生成の通常の部分に一致）。∞ filtered 余極限による compact 性と環スペクトルへの比較は含まれない。"] _root_.SerrePositivity.DifferentialGraded.moduleCompactGenerators_detect_zero
