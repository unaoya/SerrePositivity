module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor

/-!
概要：複体の零次項に加群を直積で加え、正次数の項と微分を保つ。
方針：零次の微分は第一成分への射影との合成、それ以後は元の微分。
規約：基底環と係数加群の宇宙は独立。
使われ方：F8 の C(Y) と基底の中心の零次項の和。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]
variable (C : CochainComplex (ModuleCat.{u} R) ℕ) (Q : ModuleCat.{u} R)

/-- 零次項のみを C⁰ × Q にする。 -/
def cechZeroTermExtensionTerm : ℕ → ModuleCat.{u} R
  | 0 => ModuleCat.of R (C.X 0 × Q)
  | n + 1 => C.X (n + 1)

/-- 零次では第一成分へ射影し、それ以後は元の微分を使う。 -/
def cechZeroTermExtensionDifferential :
    ∀ n, cechZeroTermExtensionTerm C Q n →ₗ[R] cechZeroTermExtensionTerm C Q (n + 1)
  | 0 => (C.d 0 1).hom.comp (LinearMap.fst R _ _)
  | n + 1 => (C.d (n + 1) (n + 2)).hom

/-- 零次項を拡張した微分も二乗零。 -/
theorem cechZeroTermExtensionDifferential_squared (n : ℕ) :
    (cechZeroTermExtensionDifferential C Q (n + 1)).comp
      (cechZeroTermExtensionDifferential C Q n) = 0 := by
  apply LinearMap.ext
  intro x
  cases n with
  | zero =>
    exact congrArg (fun f ↦ f.hom x.1) (C.d_comp_d 0 1 2)
  | succ n =>
    exact congrArg (fun f ↦ f.hom x) (C.d_comp_d (n + 1) (n + 2) (n + 3))

/-- 指定した線形微分を、元の束ねられた加群の間の射として扱う。 -/
def cechZeroTermExtensionDMap (n : ℕ) :
    cechZeroTermExtensionTerm C Q n ⟶ cechZeroTermExtensionTerm C Q (n + 1) :=
  { hom' := cechZeroTermExtensionDifferential C Q n }

/-- 零次項に中心の加群を加えた明示的な複体。 -/
def cechZeroTermExtension : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (cechZeroTermExtensionTerm C Q)
    (cechZeroTermExtensionDMap C Q) (by
      intro n
      apply ModuleCat.hom_ext
      exact cechZeroTermExtensionDifferential_squared C Q n)

/-- 拡張した複体の隣り合う項の微分は指定した線形写像。 -/
theorem cechZeroTermExtension_d (n : ℕ) :
    (cechZeroTermExtension C Q).d n (n + 1) = cechZeroTermExtensionDMap C Q n := by
  exact CochainComplex.of_d (cechZeroTermExtensionTerm C Q)
    (cechZeroTermExtensionDMap C Q) n

/-- 元の複体への射影の各次数の射。 -/
def cechZeroTermProjectionComponent : ∀ n, (cechZeroTermExtension C Q).X n ⟶ C.X n
  | 0 => ModuleCat.ofHom (LinearMap.fst R _ _)
  | n + 1 => 𝟙 (C.X (n + 1))

/-- 零次項を拡張した複体から元の複体への射影。 -/
def cechZeroTermProjection : cechZeroTermExtension C Q ⟶ C :=
  CochainComplex.ofHom (cechZeroTermProjectionComponent C Q) (by
    intro n
    cases n with
    | zero =>
      change ModuleCat.ofHom (LinearMap.fst R (C.X 0) Q) ≫ C.d 0 1 =
        (cechZeroTermExtension C Q).d 0 1 ≫ 𝟙 _
      rw [Category.comp_id]
      rw [cechZeroTermExtension_d]
      rfl
    | succ n =>
      change 𝟙 _ ≫ C.d (n + 1) (n + 2) =
        (cechZeroTermExtension C Q).d (n + 1) (n + 2) ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
      rw [cechZeroTermExtension_d]
      rfl)

/-- 射影の各次数の成分は全射。 -/
theorem cechZeroTermProjection_epi (n : ℕ) : Epi ((cechZeroTermProjection C Q).f n) := by
  cases n with
  | zero =>
    apply (ModuleCat.epi_iff_surjective _).mpr
    change Function.Surjective (LinearMap.fst R (C.X 0) Q)
    intro x
    exact ⟨(x, 0), rfl⟩
  | succ n =>
    change Epi (𝟙 (C.X (n + 1)))
    infer_instance

/-- 零次項を加えても、正次数の短複体の H は射影により同型となる。 -/
theorem cechZeroTermProjection_positive_homology_isIso (n : ℕ) :
    IsIso (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ)
        n (n + 1) (n + 2)).map (cechZeroTermProjection C Q))) := by
  let φ := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ)
    n (n + 1) (n + 2)).map (cechZeroTermProjection C Q)
  haveI : Epi φ.τ₁ := cechZeroTermProjection_epi C Q n
  haveI : IsIso φ.τ₂ := by
    change IsIso (𝟙 (C.X (n + 1)))
    infer_instance
  haveI : Mono φ.τ₃ := by
    change Mono (𝟙 (C.X (n + 2)))
    infer_instance
  haveI := ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ
  exact ShortComplex.QuasiIso.isIso φ

end SerrePositivity.AlgebraicGeometry
