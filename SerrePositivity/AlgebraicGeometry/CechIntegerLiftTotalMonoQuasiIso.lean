module

public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalColumns
public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalShortExact
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
概要：各列で単射な擬同型を、元の同じtotalへ渡す。
方針：同じ余核の短完全列と既存の長完全列を使う。
規約：正次数で全射でないsingleからの増大にも適用する。
使われ方：元のアフィンnerveのΓとタプルČechの比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
local notation "up" => ComplexShape.up ℕ

/-- 同じ短完全列の第三項が完全なら、第一の射は擬同型。 -/
theorem cechShortExact_quasiIso_f_of_acyclic_X₃
    (S : ShortComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ))
    (hS : S.ShortExact) (h₃ : S.X₃.Acyclic) : QuasiIso S.f := by
  constructor
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hz (i : ℕ) : IsZero (S.X₃.homology i) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (h₃ i)
  have he : Epi (HomologicalComplex.homologyMap S.f n) :=
    (hS.homology_exact₂ n).epi_f_iff.mpr ((hz n).eq_zero_of_tgt _)
  have hm : Mono (HomologicalComplex.homologyMap S.f n) := by
    cases n with
    | zero =>
      letI := hS.mono_f
      exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f 0 (by
        intro i hi
        change i + 1 = 0 at hi
        omega)
    | succ n =>
      exact (hS.homology_exact₁ n (n + 1) rfl).mono_g_iff.mpr
        ((hz n).eq_zero_of_src _)
  letI := he
  letI := hm
  exact isIso_of_mono_of_epi _

set_option backward.isDefEq.respectTransparency false in
/-- 元の各列の擬同型と各成分の単射性から、同じtotalの射も擬同型。 -/
theorem cechIntegerLiftTotal_quasiIso_of_mono_columns
    {K L : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up} (f : K ⟶ L)
    (hf : ∀ a, QuasiIso (f.f a))
    (hm : ∀ a b, Function.Injective (((f.f a).f b).hom)) :
    QuasiIso (HomologicalComplex₂.total.map f up) := by
  letI : Abelian (HomologicalComplex₂ (ModuleCat.{u} ℤ) up up) :=
    inferInstanceAs (Abelian (CochainComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ) ℕ))
  letI : Mono f := HomologicalComplex.mono_of_mono_f f (fun a ↦
    HomologicalComplex.mono_of_mono_f _ (fun b ↦ (ModuleCat.mono_iff_injective _).mpr
      (hm a b)))
  let S := ShortComplex.cokernelSequence f
  have hS : S.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact f
      mono_f := inferInstanceAs (Mono f)
      epi_g := inferInstanceAs (Epi (cokernel.π f)) }
  have hc : ∀ a, (S.X₃.X a).Acyclic := by
    intro a
    let E := HomologicalComplex.eval (CochainComplex (ModuleCat.{u} ℤ) ℕ) up a
    have hs := hS.map_of_exact E
    have hq : QuasiIso (S.map E).f := hf a
    exact hs.acyclic_X₃ hq
  have ht := cechIntegerLiftTotal_shortExact S hS
  have htc : (S.X₃.total up).Acyclic := cechIntegerLiftTotal_acyclic_of_columns S.X₃ hc
  exact cechShortExact_quasiIso_f_of_acyclic_X₃ (cechIntegerLiftTotalShortComplex S) ht htc

end SerrePositivity.AlgebraicGeometry
