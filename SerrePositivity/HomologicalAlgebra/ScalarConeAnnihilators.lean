module

public import SerrePositivity.HomologicalAlgebra.DerivedModuleCone
public import SerrePositivity.HomologicalAlgebra.DerivedHomologyLinear
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import SerrePositivity.CommutativeAlgebra.Localization.PowerTorsion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorAnnihilator
public import SerrePositivity.CommutativeAlgebra.ScalarIsogeny

/-! # 導来対象と写像錐のスカラーによる零化

## 概要

二段の導来対象（二つの次数にだけコホモロジーを持つ対象）では、各コホモロジーを零化するスカラーの積が対象全体を零化する。加群の写像の錐について、可換図式・始域の全射・有限主開被覆を通じて零化を移し、holim との比較と Milnor 列の一様な零化から冪の零化を得る。被約環上の有限加群から有限自由加群への写像が `g` を反転して全単射なら、その錐は `g` の冪で零になる（`finiteFreeConeIsogeny`、CLMST Claim 2.4.8 の一般形）。

## 方針

二段の対象は標準 t 構造の二項代表で扱い、零化は完全三角形の Hom の完全列から示す。

## 規約

終域の余核・有限性・平坦性は要求しない。TwoCohomologyAnnihilator は重いので最後に置く。

## 使われ方

CLMST の almost 零化と完備テンソルの同種写像、Prop 2.4.7 の証明（`finiteFreeConeIsogeny`）。
-/

@[expose] public noncomputable section

universe u v w

section TwoTermConeAnnihilatorPart

namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R]

private lemma exact_zero_apply {S : ShortComplex (ModuleCat.{u} R)}
    (_ : S.Exact) (x : S.X₁) : S.g (S.f x) = 0 := S.zero_apply x

/-- 完全三角形の両端の零化元の積は中間対象を零化する。 -/
theorem triangle_scalar_product_eq_zero
    (T : Triangle (DerivedCategory (ModuleCat.{u} R))) (hT : T ∈ distTriang _)
    (r s : R) (hr : r • 𝟙 T.obj₁ = 0) (hs : s • 𝟙 T.obj₃ = 0) :
    (r * s) • 𝟙 T.obj₂ = 0 := by
  have h : T.mor₁ ≫ (r • 𝟙 T.obj₂) = 0 := by
    rw [Linear.comp_smul, Category.comp_id, ← Category.id_comp T.mor₁,
      ← Linear.smul_comp, hr, zero_comp]
  obtain ⟨a, ha⟩ := Triangle.yoneda_exact₂ T hT (r • 𝟙 T.obj₂) h
  calc
    (r * s) • 𝟙 T.obj₂ = (r • 𝟙 T.obj₂) ≫ (s • 𝟙 T.obj₂) := by simp [smul_smul, mul_comm]
    _ = (T.mor₂ ≫ a) ≫ (s • 𝟙 T.obj₂) := by rw [ha]
    _ = T.mor₂ ≫ ((s • 𝟙 T.obj₃) ≫ a) := by simp
    _ = 0 := by rw [hs, zero_comp, comp_zero]

/-- 一次数に集中した導来対象の自己射はホモロジー上で検出できる。 -/
theorem scalar_eq_zero_of_single_homology
    (X : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) [X.IsGE n] [X.IsLE n]
    (r : R) (hr : r • 𝟙 ((DerivedCategory.homologyFunctor _ n).obj X) = 0) :
    r • 𝟙 X = 0 := by
  obtain ⟨Y, ⟨e⟩⟩ := X.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) n
  let d := H.mapIso e
  have hY : r • 𝟙 (H.obj ((DerivedCategory.singleFunctor _ n).obj Y)) = 0 := by
    rw [← cancel_epi d.hom, comp_zero]
    simpa using congrArg (fun z ↦ z ≫ d.hom) hr
  let a := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) n).app Y
  have hY' : r • 𝟙 Y = 0 := by
    rw [← cancel_epi a.hom, comp_zero]
    simpa using congrArg (fun z ↦ z ≫ a.hom) hY
  have hsingle : r • 𝟙 ((DerivedCategory.singleFunctor _ n).obj Y) = 0 := by
    simpa using congrArg (DerivedCategory.singleFunctor _ n).map hY'
  rw [← cancel_mono e.hom, zero_comp]
  simpa using congrArg (fun z ↦ e.hom ≫ z) hsingle

/-- 一次数に集中した複体のホモロジー零化を導来零射へ移す。 -/
theorem derived_scalar_eq_zero_of_single_cohomology
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) [K.IsGE n] [K.IsLE n]
    (r : R) (hr : r • 𝟙 (K.homology n) = 0) :
    r • 𝟙 (DerivedCategory.Q.obj K) = 0 := by
  apply scalar_eq_zero_of_single_homology R _ n r
  let e : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
      (DerivedCategory.Q.obj K) ≅ K.homology n :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).app K
  have hh := congrArg (fun z ↦ e.hom ≫ z) hr
  change e.hom ≫ (r • 𝟙 (K.homology n)) = 0 at hh
  rw [Linear.comp_smul, Category.comp_id] at hh
  rw [← cancel_mono e.hom, zero_comp, Linear.smul_comp, Category.id_comp]
  exact hh

/-- 二つの隣接次数だけに項を持つ複体では、両ホモロジーの零化元の積が導来対象を消す。 -/
theorem two_term_derived_scalar_product_eq_zero
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) (hab : a + 1 = b)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] (r s : R)
    (hr : r • 𝟙 (K.homology a) = 0) (hs : s • 𝟙 (K.homology b) = 0) :
    (r * s) • 𝟙 (DerivedCategory.Q.obj K) = 0 := by
  have hleft : r • 𝟙 (DerivedCategory.Q.obj (K.truncLE a)) = 0 := by
    apply derived_scalar_eq_zero_of_single_cohomology R _ a r
    let e := asIso (HomologicalComplex.homologyMap (K.ιTruncLE a) a)
    rw [← cancel_mono e.hom, zero_comp]
    simpa only [Linear.comp_smul, Linear.smul_comp, Category.comp_id,
      Category.id_comp, comp_zero] using
      congrArg (fun z ↦ e.hom ≫ z) hr
  have hright : s • 𝟙 (DerivedCategory.Q.obj (K.truncGE b)) = 0 := by
    apply derived_scalar_eq_zero_of_single_cohomology R _ b s
    let e := asIso (HomologicalComplex.homologyMap (K.πTruncGE b) b)
    rw [← cancel_epi e.hom, comp_zero]
    simpa using congrArg (fun z ↦ z ≫ e.hom) hs
  let h := K.shortComplexTruncLE_shortExact a
  let e := asIso (DerivedCategory.Q.map (K.shortComplexTruncLEX₃ToTruncGE a b hab))
  have hright' : s • 𝟙 (DerivedCategory.Q.obj (K.shortComplexTruncLE a).X₃) = 0 := by
    rw [← cancel_mono e.hom, zero_comp]
    simpa only [Linear.comp_smul, Linear.smul_comp, Category.comp_id,
      Category.id_comp, comp_zero] using
      congrArg (fun z ↦ e.hom ≫ z) hright
  exact triangle_scalar_product_eq_zero R (DerivedCategory.triangleOfSES h)
    (DerivedCategory.triangleOfSES_distinguished h) r s hleft hright'

variable {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- 加群写像の錐の項は-1次以上にある。 -/
instance moduleMapConeComplex_isStrictlyGE (f : M →ₗ[R] N) :
    (moduleMapConeComplex R f).IsStrictlyGE (-1) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  apply (CochainComplex.mappingCone.isZero_X_iff _ i).mpr
  constructor <;> exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)

/-- 加群写像の錐の項は0次以下にある。 -/
instance moduleMapConeComplex_isStrictlyLE (f : M →ₗ[R] N) :
    (moduleMapConeComplex R f).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  apply (CochainComplex.mappingCone.isZero_X_iff _ i).mpr
  constructor <;> exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)

/-- 核の零化は錐の-1次ホモロジーを零化する。 -/
theorem moduleMapCone_homology_neg_one_scalar_eq_zero
    (f : M →ₗ[R] N) (r : R) (hr : ∀ x : M, f x = 0 → r • x = 0) :
    r • 𝟙 ((moduleMapConeComplex R f).homology (-1)) = 0 := by
  let φ := moduleMapSingle R f
  let eM := HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of R M)
  let eN := HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of R N)
  have hnat := HomologicalComplex.singleObjHomologySelfIso_hom_naturality
    (.up ℤ) 0 (ModuleCat.ofHom f)
  change HomologicalComplex.homologyMap φ 0 ≫ eN.hom = eM.hom ≫ ModuleCat.ofHom f at hnat
  change r • 𝟙 ((Cone.cone φ).homology (-1)) = 0
  ext z
  change r • z = 0
  have hzker : f (eM.hom (Cone.δ φ (-1) 0 (by decide) z)) = 0 := by
    have heq := congrArg (fun t ↦ t (Cone.δ φ (-1) 0 (by decide) z)) hnat
    change eN.hom (HomologicalComplex.homologyMap φ 0
      (Cone.δ φ (-1) 0 (by decide) z)) =
        f (eM.hom (Cone.δ φ (-1) 0 (by decide) z)) at heq
    rw [← heq]
    have hh := exact_zero_apply R (Cone.exact₁ φ (-1) 0 (by decide)) z
    simpa using congrArg eN.hom hh
  have hδ : Cone.δ φ (-1) 0 (by decide) (r • z) = 0 := by
    apply (ModuleCat.mono_iff_injective eM.hom).mp inferInstance
    simpa using hr _ hzker
  obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (Cone.exact₃ φ (-1) 0 (by decide)) (r • z) hδ
  have hwzero : w = 0 := by
    have hzero := HomologicalComplex.exactAt_single_obj (.up ℤ) 0
      (ModuleCat.of R N) (-1) (by decide)
    exact ModuleCat.isZero_iff_subsingleton.mp hzero.isZero_homology |>.elim _ _
  simpa [hwzero] using hw.symm

/-- 余核の零化は錐の0次ホモロジーを零化する。 -/
theorem moduleMapCone_homology_zero_scalar_eq_zero
    (f : M →ₗ[R] N) (s : R) (hs : ∀ y : N ⧸ f.range, s • y = 0) :
    s • 𝟙 ((moduleMapConeComplex R f).homology 0) = 0 := by
  let φ := moduleMapSingle R f
  let eM := HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of R M)
  let eN := HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of R N)
  have hnat := HomologicalComplex.singleObjHomologySelfIso_hom_naturality
    (.up ℤ) 0 (ModuleCat.ofHom f)
  change HomologicalComplex.homologyMap φ 0 ≫ eN.hom = eM.hom ≫ ModuleCat.ofHom f at hnat
  change s • 𝟙 ((Cone.cone φ).homology 0) = 0
  ext z
  change s • z = 0
  have hδ : Cone.δ φ 0 1 (by decide) z = 0 := by
    have hzero := HomologicalComplex.exactAt_single_obj (.up ℤ) 0
      (ModuleCat.of R M) 1 (by decide)
    exact ModuleCat.isZero_iff_subsingleton.mp hzero.isZero_homology |>.elim _ _
  obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (Cone.exact₃ φ 0 1 (by decide)) z hδ
  have hmem : s • eN.hom w ∈ f.range := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact (map_smul f.range.mkQ s (eN.hom w)).trans (hs _)
  obtain ⟨m, hm⟩ := hmem
  have hmap : HomologicalComplex.homologyMap φ 0 (eM.inv m) = s • w := by
    apply (ModuleCat.mono_iff_injective eN.hom).mp inferInstance
    have heq := congrArg (fun t ↦ t (eM.inv m)) hnat
    change eN.hom (HomologicalComplex.homologyMap φ 0 (eM.inv m)) =
      f (eM.hom (eM.inv m)) at heq
    simpa only [Iso.inv_hom_id_apply, map_smul, hm] using heq
  have hz := exact_zero_apply R (Cone.exact₂ φ 0) (eM.inv m)
  change HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr φ) 0
    (HomologicalComplex.homologyMap φ 0 (eM.inv m)) = 0 at hz
  rw [hmap, map_smul, hw] at hz
  exact hz

/-- 任意の加群写像について、核と余核の零化元の積が実導来錐上の零射となる。 -/
theorem moduleMapConeScalar_eq_zero_of_ker_coker_annihilated
    (f : M →ₗ[R] N) (r s : R)
    (hr : ∀ x : M, f x = 0 → r • x = 0)
    (hs : ∀ y : N ⧸ f.range, s • y = 0) :
    moduleMapConeScalar R f (r * s) = 0 :=
  two_term_derived_scalar_product_eq_zero R (moduleMapConeComplex R f) (-1) 0
    (by decide) r s (moduleMapCone_homology_neg_one_scalar_eq_zero R f r hr)
    (moduleMapCone_homology_zero_scalar_eq_zero R f s hs)

end SerrePositivity

end TwoTermConeAnnihilatorPart

section ConeComparisonSquarePart

namespace SerrePositivity
variable {R M N : Type u} {L : Type v} {P : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup L] [Module R L]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- 三辺の実比較から元の写像の核・余核の具体的な零化因子を得る。 -/
theorem ker_coker_annihilated_of_comparison_square
    (f : M →ₗ[R] N) (s : M →ₗ[R] L) (h : L →ₗ[R] P) (t : N →ₗ[R] P)
    (hsq : t.comp f = h.comp s) (a b c d e : R)
    (hsk : ∀ x : s.ker, a • x = 0) (hsc : ∀ y : L ⧸ s.range, b • y = 0)
    (hhk : ∀ x : h.ker, c • x = 0) (hhc : ∀ y : P ⧸ h.range, d • y = 0)
    (htk : ∀ x : t.ker, e • x = 0) :
    (∀ x : f.ker, (a * c) • x = 0) ∧
      (∀ y : N ⧸ f.range, (e * b * d) • y = 0) := by
  have hs (x : M) : t (f x) = h (s x) := LinearMap.congr_fun hsq x
  constructor
  · intro x
    apply Subtype.ext
    change (a * c) • (x : M) = 0
    have hh : h (s (x : M)) = 0 := by rw [← hs, x.property, map_zero]
    have hcs : c • s (x : M) = 0 := congrArg Subtype.val (hhk ⟨s x, hh⟩)
    have hscx : s (c • (x : M)) = 0 := (s.map_smul c x).trans hcs
    have hac : a • (c • (x : M)) = 0 := congrArg Subtype.val (hsk ⟨c • x, hscx⟩)
    simpa only [mul_smul] using hac
  · intro y
    obtain ⟨y, rfl⟩ := f.range.mkQ_surjective y
    have hdy : d • t y ∈ h.range := by
      apply (Submodule.Quotient.mk_eq_zero h.range).mp
      exact (h.range.mkQ.map_smul d (t y)).trans (hhc _)
    obtain ⟨z, hz⟩ := hdy
    have hbz : b • z ∈ s.range := by
      apply (Submodule.Quotient.mk_eq_zero s.range).mp
      exact (s.range.mkQ.map_smul b z).trans (hsc _)
    obtain ⟨x, hx⟩ := hbz
    have hcomp : h (s x) = (b * d) • t y := by
      rw [hx, map_smul, hz, smul_smul]
    have hzero : t ((b * d) • y - f x) = 0 := by
      rw [map_sub, map_smul, hs, hcomp, sub_self]
    have he : e • ((b * d) • y - f x) = 0 :=
      congrArg Subtype.val (htk ⟨(b * d) • y - f x, hzero⟩)
    have he' : (e * b * d) • y = f (e • x) := by
      rw [smul_sub, smul_smul, ← f.map_smul, sub_eq_zero] at he
      simpa only [mul_assoc] using he
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero f.range).mpr
    exact ⟨e • x, he'.symm⟩

/-- 同じ元の可換図式から、元の実錐のスカラー射を零にする。 -/
theorem moduleMapConeScalar_of_comparison_square
    (f : M →ₗ[R] N) (s : M →ₗ[R] L) (h : L →ₗ[R] P) (t : N →ₗ[R] P)
    (hsq : t.comp f = h.comp s) (a b c d e : R)
    (hsk : ∀ x : s.ker, a • x = 0) (hsc : ∀ y : L ⧸ s.range, b • y = 0)
    (hhk : ∀ x : h.ker, c • x = 0) (hhc : ∀ y : P ⧸ h.range, d • y = 0)
    (htk : ∀ x : t.ker, e • x = 0) :
    moduleMapConeScalar R f ((a * c) * (e * b * d)) = 0 := by
  obtain ⟨hk, hc⟩ := ker_coker_annihilated_of_comparison_square f s h t hsq
    a b c d e hsk hsc hhk hhc htk
  apply moduleMapConeScalar_eq_zero_of_ker_coker_annihilated R f
  · intro x hx
    exact congrArg Subtype.val (hk ⟨x, hx⟩)
  · exact hc

end SerrePositivity

end ConeComparisonSquarePart

section ConeOfSurjectiveSourcePart

namespace SerrePositivity
variable {R L M N : Type u} [CommRing R]
    [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

/-- 全射な始域変更の下で、元の錐の零射から変更後の錐の零射を得る。
核と余核を各々移すため、スカラーは二乗となる。 -/
theorem moduleMapConeScalar_of_surjective_source
    (t : L →ₗ[R] M) (ht : Function.Surjective t)
    (α : M →ₗ[R] N) (β : L →ₗ[R] N) (hsq : α.comp t = β)
    (g : R) (q : ℕ) (hβ : moduleMapConeScalar R β (g ^ q) = 0) :
    moduleMapConeScalar R α (g ^ (2 * q)) = 0 := by
  obtain ⟨hk, hc⟩ := moduleMapCone_pow_scalar_eq_zero_annihilates R β g q hβ
  have hs (x : L) : α (t x) = β x := LinearMap.congr_fun hsq x
  rw [two_mul, pow_add]
  apply moduleMapConeScalar_eq_zero_of_ker_coker_annihilated R α
  · intro y hy
    obtain ⟨x, rfl⟩ := ht y
    have hx : β x = 0 := (hs x).symm.trans hy
    have he := congrArg (fun z : β.ker => t z) (hk ⟨x, hx⟩)
    simpa only [Submodule.coe_smul, map_smul, Submodule.coe_zero, map_zero] using he
  · intro y
    obtain ⟨y, rfl⟩ := α.range.mkQ_surjective y
    have hm : g ^ q • y ∈ β.range := by
      apply (Submodule.Quotient.mk_eq_zero β.range).mp
      exact (map_smul β.range.mkQ (g ^ q) y).trans (hc _)
    obtain ⟨x, hx⟩ := hm
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero α.range).mpr
    exact ⟨t x, (hs x).trans hx⟩

end SerrePositivity

end ConeOfSurjectiveSourcePart

section ConeFiniteCoverPart

namespace SerrePositivity
set_option backward.isDefEq.respectTransparency false

/-- 有限被覆上の局所錐零化を、既存の加群族の指数合流で元の g へ戻す。
大域的な一つの有限自由比較を要求しない。 -/
theorem moduleMapConeScalar_of_finite_cover
    {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (g : R) (t : Finset R)
    (hcover : ∃ k : ℕ, g ^ k ∈ Ideal.span (t : Set R))
    (hlocal : ∀ a ∈ t, ∃ q : ℕ, moduleMapConeScalar R f (a ^ q) = 0) :
    ∃ q : ℕ, moduleMapConeScalar R f (g ^ q) = 0 := by
  obtain ⟨q, hq⟩ := exists_uniform_family_pow_smul_zero_of_cover
    (fun _ : Unit => f.ker × (N ⧸ f.range)) g t hcover (by
      intro a ha
      obtain ⟨q, hq⟩ := hlocal a ha
      obtain ⟨hk, hc⟩ := moduleMapCone_pow_scalar_eq_zero_annihilates R f a q hq
      exact ⟨q, fun _ x => Prod.ext (hk x.1) (hc x.2)⟩)
  refine ⟨2 * q, ?_⟩
  rw [two_mul, pow_add]
  apply moduleMapConeScalar_eq_zero_of_ker_coker_annihilated R f
  · intro x hx
    exact congrArg (fun z : f.ker × (N ⧸ f.range) => (z.1 : M))
      (hq () (⟨x, hx⟩, 0))
  · intro y
    exact congrArg Prod.snd (hq () (0, y))

end SerrePositivity

end ConeFiniteCoverPart

section TwoCohomologyAnnihilatorPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 二つの隣接次数にコホモロジーを持つ任意の実導来対象の零化。
代表複体の各項の射影性や、厳密な二項性を入力に要求しない。 -/
theorem two_cohomology_scalar_product_eq_zero
    (X : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) (hab : a + 1 = b)
    [X.IsGE a] [X.IsLE b] (r s : R)
    (hr : r • 𝟙 ((DerivedCategory.homologyFunctor _ a).obj X) = 0)
    (hs : s • 𝟙 ((DerivedCategory.homologyFunctor _ b).obj X) = 0) :
    (r * s) • 𝟙 X = 0 := by
  obtain ⟨K, hKa, hKb, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isGE_of_isLE a b
  let _ := hKa
  let _ := hKb
  let da : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) a).obj X ≅ K.homology a :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) a).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors _ a).app K
  let db : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) b).obj X ≅ K.homology b :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) b).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors _ b).app K
  have ha : r • 𝟙 (K.homology a) = 0 := by
    rw [← cancel_epi da.hom, comp_zero, Linear.comp_smul, Category.comp_id]
    simpa using congrArg (fun z ↦ z ≫ da.hom) hr
  have hb : s • 𝟙 (K.homology b) = 0 := by
    rw [← cancel_epi db.hom, comp_zero, Linear.comp_smul, Category.comp_id]
    simpa using congrArg (fun z ↦ z ≫ db.hom) hs
  have hK := two_term_derived_scalar_product_eq_zero R K a b hab r s ha hb
  rw [← cancel_mono e.hom, zero_comp]
  simpa using congrArg (fun z ↦ e.hom ≫ z) hK

/-- ホモロジー上の同じgᴺによる零化から、対象上のg²ᴺの零射を得る。 -/
theorem two_cohomology_scalar_pow_eq_zero
    (X : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) (hab : a + 1 = b)
    [X.IsGE a] [X.IsLE b] (g : R) (N : ℕ)
    (ha : ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) a).obj X, g ^ N • x = 0)
    (hb : ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) b).obj X, g ^ N • x = 0) :
    g ^ (2 * N) • 𝟙 X = 0 := by
  have hr : g ^ N • 𝟙 ((DerivedCategory.homologyFunctor _ a).obj X) = 0 := by
    ext x
    exact ha x
  have hs : g ^ N • 𝟙 ((DerivedCategory.homologyFunctor _ b).obj X) = 0 := by
    ext x
    exact hb x
  rw [two_mul, pow_add]
  exact two_cohomology_scalar_product_eq_zero R X a b hab _ _ hr hs

/-- 一様な段ごとの零化をholim比較と二次数性を通じて実導来零射へ移す。
必要な隣接次数を両方のMilnor列で明示し、段ごとの指数を一様と取り違えない。 -/
theorem two_cohomology_scalar_pow_eq_zero_of_iso_homotopyLimit
    (X : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) (hab : a + 1 = b)
    [X.IsGE a] [X.IsLE b]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
    (e : X ≅ DerivedCompletion.complexTowerHomotopyLimitObject R K t) (g : R) (N : ℕ)
    (ha : ∀ n, (∀ x : (K n).homology a, g ^ N • x = 0) ∧
      (∀ x : (K n).homology (a - 1), g ^ N • x = 0))
    (hb : ∀ n, (∀ x : (K n).homology b, g ^ N • x = 0) ∧
      (∀ x : (K n).homology (b - 1), g ^ N • x = 0)) :
    g ^ (4 * N) • 𝟙 X = 0 := by
  have he : 4 * N = 2 * (2 * N) := by omega
  rw [he]
  apply two_cohomology_scalar_pow_eq_zero R X a b hab g (2 * N)
  · exact DerivedCompletion.derived_homology_pow_annihilated_of_iso_homotopyLimit R K t X e a g N ha
  · exact DerivedCompletion.derived_homology_pow_annihilated_of_iso_homotopyLimit R K t X e b g N hb

/-- 加群写像の実導来錐に対する、公開cone APIへの接続。 -/
theorem moduleMapConeScalar_pow_eq_zero_of_iso_homotopyLimit
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)
    (t : ∀ n, K (n + 1) ⟶ K n)
    (e : moduleMapCone R f ≅ DerivedCompletion.complexTowerHomotopyLimitObject R K t)
    (g : R) (q : ℕ)
    (ha : ∀ n, (∀ x : (K n).homology (-1), g ^ q • x = 0) ∧
      (∀ x : (K n).homology (-2), g ^ q • x = 0))
    (hb : ∀ n, (∀ x : (K n).homology 0, g ^ q • x = 0) ∧
      (∀ x : (K n).homology (-1), g ^ q • x = 0)) :
    moduleMapConeScalar R f (g ^ (4 * q)) = 0 := by
  have : (moduleMapCone R f).IsGE (-1) := by
    change (DerivedCategory.Q.obj (moduleMapConeComplex R f)).IsGE (-1)
    infer_instance
  have : (moduleMapCone R f).IsLE 0 := by
    change (DerivedCategory.Q.obj (moduleMapConeComplex R f)).IsLE 0
    infer_instance
  exact two_cohomology_scalar_pow_eq_zero_of_iso_homotopyLimit R (moduleMapCone R f)
    (-1) 0 (by norm_num) K t e g q ha hb

end SerrePositivity

end TwoCohomologyAnnihilatorPart

section FiniteFreeConeIsogenyPart

namespace SerrePositivity
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R] [IsReduced R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- 核をg^a、余核をg^bが消すとき、錐はg^(a+b)で零化される。 -/
theorem finiteFreeConeIsogeny (g : R) (r : ℕ) (f : M →ₗ[R] (Fin r → R))
    (hf : Function.Bijective (awayModuleMap g f)) :
    ∃ n : ℕ, moduleMapConeScalar R f (g ^ n) = 0 := by
  obtain ⟨a, b, ha, hb⟩ := exists_pow_ker_coker_annihilator g r f hf
  refine ⟨a + b, ?_⟩
  rw [pow_add]
  exact moduleMapConeScalar_eq_zero_of_ker_coker_annihilated R f (g ^ a) (g ^ b) ha hb

/-- 同じg冪による核・余核の零化と、実導来錐の零射を同時に公開する。 -/
theorem finiteFreeConeIsogeny_with_annihilators
    (g : R) (r : ℕ) (f : M →ₗ[R] (Fin r → R))
    (hf : Function.Bijective (awayModuleMap g f)) :
    ∃ n : ℕ, moduleMapConeScalar R f (g ^ n) = 0 ∧
      (∀ x : f.ker, g ^ n • x = 0) ∧
      (∀ y : (Fin r → R) ⧸ f.range, g ^ n • y = 0) := by
  obtain ⟨n, hn⟩ := finiteFreeConeIsogeny R g r f hf
  exact ⟨n, hn, moduleMapCone_pow_scalar_eq_zero_annihilates R f g n hn⟩

end SerrePositivity

end FiniteFreeConeIsogenyPart
