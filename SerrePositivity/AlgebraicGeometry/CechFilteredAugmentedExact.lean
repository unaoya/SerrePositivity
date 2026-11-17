module

public import SerrePositivity.AlgebraicGeometry.CechFilteredAugmentedDifferential
public import SerrePositivity.AlgebraicGeometry.ProjectiveFilteredHomology
public import SerrePositivity.AlgebraicGeometry.CechFiniteIndexOrder
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechSplitExact
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
概要：長さ0を含む同じ Čech の完全性を filtered 余極限へ渡す。
方針：既存の各項の標準比較と、加群の filtered 余極限の完全性を使う。
規約：元の微分と増大項を変更しない。
使われ方：アフィン被覆の増大完全性を Frobenius の係数に渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι] [Fintype ι]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (D : J ⥤ Finset ι ⥤ ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
/-- 有限被覆の増大項からの同じ微分の単射性は、filtered 余極限へ移る。 -/
theorem fullCechFiltered_injective_zero
    (h : ∀ j, Function.Injective (fullCechDifferential (D.obj j) 0)) :
    Function.Injective (fullCechDifferential (colimit D) 0) := by
  letI := moduleCatFiltered_hasExactColimitsOfShape R J
  let η := Functor.whiskerLeft D (fullCechDifferentialNatTrans 0)
  let e₀ := preservesColimitIso (projectiveCechCochainsFunctor (R := R) (ι := ι) 0) D
  let e₁ := preservesColimitIso (projectiveCechCochainsFunctor (R := R) (ι := ι) 1) D
  haveI (j : J) : Mono (η.app j) := (ModuleCat.mono_iff_injective _).mpr (h j)
  haveI : Mono η := NatTrans.mono_of_mono_app η
  haveI : Mono (colim.map η) := inferInstance
  let d := ModuleCat.ofHom (fullCechDifferential (colimit D) 0)
  have hc : colim.map η ≫ e₁.inv = e₀.inv ≫ d :=
    fullCechFilteredDifferential_compare D 0
  have he : e₀.hom ≫ colim.map η ≫ e₁.inv = d := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      congrArg (fun t ↦ e₀.hom ≫ t) hc
  haveI : Mono d := by
    rw [← he]
    infer_instance
  exact (ModuleCat.mono_iff_injective d).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- 各有限段の同じ全タプル Čech 微分の完全性は、増大から全長さで余極限へ移る。 -/
theorem fullCechFiltered_exact (k : ℕ)
    (h : ∀ j, Function.Exact (fullCechDifferential (D.obj j) k)
      (fullCechDifferential (D.obj j) (k + 1))) :
    Function.Exact (fullCechDifferential (colimit D) k)
      (fullCechDifferential (colimit D) (k + 1)) := by
  letI : LinearOrder ι := cechFiniteIndexOrder ι
  letI := moduleCatFiltered_hasExactColimitsOfShape R J
  let S : ShortComplex (J ⥤ ModuleCat.{u} R) :=
    ShortComplex.mk (Functor.whiskerLeft D (fullCechDifferentialNatTrans k))
      (Functor.whiskerLeft D (fullCechDifferentialNatTrans (k + 1))) (by
        apply NatTrans.ext
        funext j
        apply ModuleCat.hom_ext
        exact fullCechAugmentedDifferential_squared (D.obj j) k)
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
    apply NatTrans.ext
    funext j
    have hj : (S.map ((evaluation J (ModuleCat.{u} R)).obj j)).Exact := by
      apply (ShortComplex.moduleCat_exact_iff _).mpr
      intro x hx
      exact (h j x).mp hx
    have hz := (ShortComplex.exact_iff_isZero_homology _).mp hj
    have hz' := IsZero.of_iso hz (S.mapHomologyIso ((evaluation J (ModuleCat.{u} R)).obj j)).symm
    exact hz'.eq_of_tgt _ _
  have hm := hS.map (colim (J := J) (C := ModuleCat.{u} R))
  let T := ShortComplex.moduleCatMk (fullCechDifferential (colimit D) k)
    (fullCechDifferential (colimit D) (k + 1))
      (fullCechAugmentedDifferential_squared (colimit D) k)
  have hT : T.Exact := by
    apply ShortComplex.exact_of_iso ?_ hm
    exact ShortComplex.isoMk
      (preservesColimitIso (projectiveCechCochainsFunctor k) D).symm
      (preservesColimitIso (projectiveCechCochainsFunctor (k + 1)) D).symm
      (preservesColimitIso (projectiveCechCochainsFunctor (k + 2)) D).symm
      (fullCechFilteredDifferential_compare D k).symm
      (fullCechFilteredDifferential_compare D (k + 1)).symm
  intro x
  constructor
  · exact ((ShortComplex.moduleCat_exact_iff T).mp hT) x
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (fullCechAugmentedDifferential_squared (colimit D) k) y

end SerrePositivity.AlgebraicGeometry
