module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.FlatProduct
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Span

/-!
概要：KST §5、Stacks 05FS・00MB の局所化と主イデアル進完備化の忠実平坦被覆。
方針：積の平坦性と、各極大イデアルの剰余体への実際の環準同型を使う。
規約：局所化する元の非零性・正則性は要求しない。
使われ方：幾何学的整な代数の射影性の局所化・完備化への帰着。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry

/--
概要：各極大イデアルの剰余体への可換な環写像を持つ平坦代数は忠実平坦。
方針：極大イデアルの拡大を写像の核に入れ、拡大イデアルが全体にならないことを示す。
規約：KST §5、Stacks 05FS、元の環の Noether 性はこの判定には不要。
使われ方：局所化と完備化の積の忠実性。
-/
theorem faithfullyFlat_of_residue_maps
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T] [Module.Flat R T]
    (hres : ∀ (m : Ideal R) [m.IsMaximal], ∃ φ : T →+* R ⧸ m,
      ∀ r : R, φ (algebraMap R T r) = Ideal.Quotient.mk m r) :
    Module.FaithfullyFlat R T := by
  constructor
  intro m hm htop
  let := hm
  obtain ⟨φ, hφ⟩ := hres m
  have hmap : m.map (algebraMap R T) ≤ RingHom.ker φ := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change φ (algebraMap R T r) = 0
    rw [hφ]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
  rw [Ideal.smul_top_eq_map] at htop
  have htop' : m.map (algebraMap R T) = ⊤ :=
    (Submodule.restrictScalars_eq_top_iff R T T).mp htop
  have h1 : (1 : T) ∈ RingHom.ker φ := hmap (htop' ▸ Submodule.mem_top)
  change φ 1 = 0 at h1
  exact one_ne_zero (by simpa only [map_one] using h1)

/--
概要：局所化と主イデアル進完備化の積から、各極大イデアルの剰余体への可換な環写像がある。
方針：元が極大イデアルの外なら局所化、内なら完備化の一段評価を使う。
規約：KST §5、Stacks 05FS、Noether 性・元の正則性は写像の構成には不要。
使われ方：積環の忠実平坦性を剰余体写像で判定する。
-/
theorem exists_residue_map_localization_completion
    {R : Type u} [CommRing R] (f : R) (m : Ideal R) [m.IsMaximal] :
    ∃ φ : (Localization.Away f × AdicCompletion (Ideal.span {f}) R) →+* R ⧸ m,
      ∀ r : R, φ (algebraMap R _ r) = Ideal.Quotient.mk m r := by
  let := Ideal.Quotient.field m
  by_cases hf : f ∈ m
  · let I : Ideal R := Ideal.span {f}
    have hIm : I ^ 1 ≤ m := by
      rw [pow_one]
      exact (Ideal.span_singleton_le_iff_mem m).mpr hf
    let ψ := (Ideal.Quotient.factor hIm).comp (AdicCompletion.evalₐ I 1).toRingHom
    refine ⟨ψ.comp (RingHom.snd _ _), ?_⟩
    intro r
    change Ideal.Quotient.factor hIm
      (AdicCompletion.evalₐ I 1 (AdicCompletion.of I R r)) = Ideal.Quotient.mk m r
    rw [AdicCompletion.evalₐ_of]
    rfl
  · have hu : IsUnit (Ideal.Quotient.mk m f) :=
      (isUnit_iff_ne_zero (a := Ideal.Quotient.mk m f)).mpr
        (fun h => hf (Ideal.Quotient.eq_zero_iff_mem.mp h))
    let ψ : Localization.Away f →+* R ⧸ m := IsLocalization.Away.lift f hu
    refine ⟨ψ.comp (RingHom.fst _ _), ?_⟩
    intro r
    change ψ (algebraMap R (Localization.Away f) r) = Ideal.Quotient.mk m r
    exact IsLocalization.Away.lift_eq (S := Localization.Away f) f hu r

/--
概要：Noether 環の局所化と主イデアル進完備化の積は、元の環上忠実平坦。
方針：局所化と完備化の平坦性を有限積へ移し、各剰余体への写像を適用する。
規約：KST §5、Stacks 05FS・00MB、任意の元に対して成立する。
使われ方：代数の射影性の忠実平坦降下の被覆環。
-/
theorem faithfullyFlat_localization_completion_product
    {R : Type u} [CommRing R] [IsNoetherianRing R] (f : R) :
    Module.FaithfullyFlat R
      (Localization.Away f × AdicCompletion (Ideal.span {f}) R) := by
  let := flat_product (R := R) (M := Localization.Away f)
    (N := AdicCompletion (Ideal.span {f}) R)
  exact faithfullyFlat_of_residue_maps (fun m _ => exists_residue_map_localization_completion f m)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
