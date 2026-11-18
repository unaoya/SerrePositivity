module

public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareLeftRight
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
概要：同じF8の中心側・Y側の包含と射影は短完全列を作る。
方針：元の各次数の直積の包含と射影で、単射・完全性・全射を照合する。
規約：同じ全複体の項と射を用い、コホモロジーの仮定は加えない。
使われ方：実際のF8図式の核の短完全列への比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u v
variable {R : Type v} [CommRing R]
namespace CechAugmentedSquare
variable (s : CechAugmentedSquare.{u} R)

/-- 元の同じ二つの全複体の射からなる短複体。 -/
def leftRightShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (Map.rightInclusion s).totalComplexMap (Map.leftProjection s).totalComplexMap
    (rightInclusion_leftProjection s)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ中心側・元の四角形・Y側の全複体は各次数で短完全。 -/
theorem leftRight_shortExact : (leftRightShortComplex s).ShortExact := by
  letI : Subsingleton (0 : ModuleCat.{u} R) :=
    ModuleCat.subsingleton_of_isZero (isZero_zero _)
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  cases n with
  | zero =>
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
      change Function.Exact (0 : (0 : ModuleCat.{u} R) →ₗ[R] s.base) LinearMap.id
      exact (LinearMap.exact_zero_iff_injective (0 : ModuleCat.{u} R) LinearMap.id).mpr
        Function.injective_id
    · apply (ModuleCat.mono_iff_injective _).mpr
      intro x y _
      exact (ModuleCat.subsingleton_of_isZero (isZero_zero (ModuleCat.{u} R))).elim x y
    · apply (ModuleCat.epi_iff_surjective _).mpr
      change Function.Surjective (LinearMap.id : s.base →ₗ[R] s.base)
      exact Function.surjective_id
  | succ n =>
    cases n with
    | zero =>
      refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
      · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
        change Function.Exact
          (fun x : (0 : ModuleCat.{u} R) × s.centerBase ↦ ((0, x.2) : s.C.X 0 × s.centerBase))
          (fun x : s.C.X 0 × s.centerBase ↦ ((x.1, 0) : s.C.X 0 × (0 : ModuleCat.{u} R)))
        intro x
        constructor
        · intro hx
          refine ⟨(0, x.2), ?_⟩
          exact Prod.ext (congrArg Prod.fst hx).symm rfl
        · rintro ⟨y, rfl⟩
          rfl
      · apply (ModuleCat.mono_iff_injective _).mpr
        change Function.Injective
          (fun x : (0 : ModuleCat.{u} R) × s.centerBase ↦ ((0, x.2) : s.C.X 0 × s.centerBase))
        intro x y h
        exact Prod.ext (Subsingleton.elim _ _) (congrArg (fun z : s.C.X 0 × s.centerBase ↦ z.2) h)
      · apply (ModuleCat.epi_iff_surjective _).mpr
        change Function.Surjective
          (fun x : s.C.X 0 × s.centerBase ↦ ((x.1, 0) : s.C.X 0 × (0 : ModuleCat.{u} R)))
        intro x
        exact ⟨(x.1, 0), Prod.ext rfl (Subsingleton.elim _ _)⟩
    | succ n =>
      refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
      · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
        change Function.Exact
          (fun x : s.E.X n × (0 : ModuleCat.{u} R) ↦ ((x.1, 0) : s.E.X n × s.C.X (n + 1)))
          (fun x : s.E.X n × s.C.X (n + 1) ↦ ((0, x.2) : (0 : ModuleCat.{u} R) × s.C.X (n + 1)))
        intro x
        constructor
        · intro hx
          refine ⟨(x.1, 0), ?_⟩
          exact Prod.ext rfl (congrArg Prod.snd hx).symm
        · rintro ⟨y, rfl⟩
          rfl
      · apply (ModuleCat.mono_iff_injective _).mpr
        change Function.Injective
          (fun x : s.E.X n × (0 : ModuleCat.{u} R) ↦ ((x.1, 0) : s.E.X n × s.C.X (n + 1)))
        intro x y h
        exact Prod.ext (congrArg (fun z : s.E.X n × s.C.X (n + 1) ↦ z.1) h) (Subsingleton.elim _ _)
      · apply (ModuleCat.epi_iff_surjective _).mpr
        change Function.Surjective
          (fun x : s.E.X n × s.C.X (n + 1) ↦ ((0, x.2) : (0 : ModuleCat.{u} R) × s.C.X (n + 1)))
        intro x
        exact ⟨(0, x.2), Prod.ext (Subsingleton.elim _ _) rfl⟩

end CechAugmentedSquare
end SerrePositivity.AlgebraicGeometry
