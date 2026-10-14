module

public import SerrePositivity.HomologicalAlgebra.TwoTermConeAnnihilator
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorAnnihilator

/-! # 二次数にコホモロジーを持つ任意の導来対象の零化

厳密な二項複体を最初から指定せず、標準t構造による二項代表を使う。
Milnor列の一様零化と組み合わせると、与えられたholim比較からg⁴ᴺの零射を得る。
-/

@[expose] public noncomputable section
universe u
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
