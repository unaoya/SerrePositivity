module

public import SerrePositivity.AlgebraicGeometry.CechLocalizationCochains
public import SerrePositivity.AlgebraicGeometry.CechLocalizedAwayRestriction
public import SerrePositivity.AlgebraicGeometry.AffineModuleCechUnit
public import Mathlib.RingTheory.LocalProperties.Exactness

/-!
概要：単位イデアルを生成する元のアフィン標準被覆の Čech 完全性を局所化で示す。
方針：各被覆元で局所化すると頂点挿入が可逆になり、有限積との比較で完全性を戻す。
規約：増大項は長さ零のコチェイン。元の加群との同定は別に扱う。
使われ方：共通アフィン細分の交叉上の完全性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {A : Type u} [CommRing A] {ι : Type} [LinearOrder ι] [Fintype ι]
variable (M : Type u) [AddCommGroup M] [Module A M] (f : ι → A)

/-- 被覆元で局所化すれば、その頂点を交叉へ挿入する制限はすべて同型。 -/
theorem affineModuleLocalizedCechInsertionIsIso (v : ι) :
    ∀ T, IsIso ((fullCechInsertVertexMap
      (affineModuleCechDiagram M f ⋙ projectiveLocalizedModuleFunctor (.powers (f v))) v).app T) := by
  intro T
  change IsIso ((projectiveLocalizedModuleFunctor (.powers (f v))).map
    ((affineModuleCechDiagram M f).map (homOfLE (Finset.subset_insert v T))))
  by_cases h : v ∈ T
  · have he : (homOfLE (Finset.subset_insert v T) : T ⟶ insert v T) =
        eqToHom (Finset.insert_eq_of_mem h).symm := Subsingleton.elim _ _
    rw [he]
    infer_instance
  · have hg : affineCechDenominator f (insert v T) = affineCechDenominator f T * f v := by
      simp only [affineCechDenominator, Finset.prod_insert h]
      ac_rfl
    change IsIso (ModuleCat.ofHom (cechLocalizedAwayRestriction (M := M) (.powers (f v))
      (affineCechDenominator_dvd f (Finset.subset_insert v T))))
    exact cechLocalizedAwayRestriction_isIso (.powers (f v)) hg ⟨1, pow_one _⟩

/-- 各被覆元で局所化すると、増大項からの写像は単射。 -/
theorem affineModuleCech_localized_zero_injective (v : ι) :
    Function.Injective (cechLocalizedCochainsDifferential (.powers (f v))
      (affineModuleCechDiagram M f) 0) := by
  let D := affineModuleCechDiagram M f
  let S := Submonoid.powers (f v)
  letI := affineModuleLocalizedCechInsertionIsIso M f v
  intro x y hxy
  apply (cechLocalizationCochainsEquiv S D 0).injective
  apply fullCechSplitVertexDifferential_zero_injective (D ⋙ projectiveLocalizedModuleFunctor S) v
  rw [← cechLocalizationCochainsEquiv_differential_apply,
    ← cechLocalizationCochainsEquiv_differential_apply, hxy]

/-- 各被覆元で局所化した、連続する Čech の余境界は完全。 -/
theorem affineModuleCech_localized_exact (v : ι) (k : ℕ) :
    Function.Exact (cechLocalizedCochainsDifferential (.powers (f v)) (affineModuleCechDiagram M f) k)
      (cechLocalizedCochainsDifferential (.powers (f v)) (affineModuleCechDiagram M f) (k + 1)) := by
  let D := affineModuleCechDiagram M f
  let S := Submonoid.powers (f v)
  letI := affineModuleLocalizedCechInsertionIsIso M f v
  apply cechLocalizationCochains_exact_of_exact S D k
  intro x
  constructor
  · exact fullCechSplitVertex_cycle_boundary (D ⋙ projectiveLocalizedModuleFunctor S) v k x
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun
      (fullCechAugmentedDifferential_squared (D ⋙ projectiveLocalizedModuleFunctor S) k) y

/-- 単位イデアルを生成する元の標準被覆では、増大項の写像は単射。 -/
theorem affineModuleCech_zero_injective (hspan : Ideal.span (Set.range f) = ⊤) :
    Function.Injective (fullCechDifferential (affineModuleCechDiagram M f) 0) := by
  let D := affineModuleCechDiagram M f
  apply injective_of_isLocalized_span (Set.range f) hspan
    (fun r ↦ LocalizedModule (.powers r.val) (FullCechCochains D 0))
    (fun _ ↦ LocalizedModule.mkLinearMap _ _)
    (fun r ↦ LocalizedModule (.powers r.val) (FullCechCochains D 1))
    (fun _ ↦ LocalizedModule.mkLinearMap _ _)
    (fullCechDifferential D 0)
  intro r
  rcases r with ⟨r, v, rfl⟩
  exact affineModuleCech_localized_zero_injective M f v

/-- 標準アフィン被覆の増大 Čech の完全性。
原典 Stacks 30.2.1 の Hⁱ の消滅に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem affineModuleCech_exact (hspan : Ideal.span (Set.range f) = ⊤) (k : ℕ) :
    Function.Exact (fullCechDifferential (affineModuleCechDiagram M f) k)
      (fullCechDifferential (affineModuleCechDiagram M f) (k + 1)) := by
  let D := affineModuleCechDiagram M f
  apply exact_of_isLocalized_span (Set.range f) hspan
    (fun r ↦ LocalizedModule (.powers r.val) (FullCechCochains D k))
    (fun _ ↦ LocalizedModule.mkLinearMap _ _)
    (fun r ↦ LocalizedModule (.powers r.val) (FullCechCochains D (k + 1)))
    (fun _ ↦ LocalizedModule.mkLinearMap _ _)
    (fun r ↦ LocalizedModule (.powers r.val) (FullCechCochains D (k + 2)))
    (fun _ ↦ LocalizedModule.mkLinearMap _ _)
    (fullCechDifferential D k) (fullCechDifferential D (k + 1))
  intro r
  rcases r with ⟨r, v, rfl⟩
  exact affineModuleCech_localized_exact M f v k

end SerrePositivity.AlgebraicGeometry
