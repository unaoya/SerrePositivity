module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
概要：有限個の整元を、有限かつ有限表示な代数の像として同時に表示する。
方針：モニック多項式の根を一つずつ加え、有限性と有限表示性を合成する。
規約：係数環の Noether 性は仮定しない。有限生成部分代数の有限表示性を仮定しない。
使われ方：Rydh 3.10 の整全射を、有限・有限表示な段で近似する入口。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- 有限個の整元は、有限かつ有限表示の R-代数から B への射の像に同時に入る。 -/
theorem exists_finite_finitePresentation_model_of_integral_family
    (n : ℕ) (b : Fin n → B) (hb : ∀ i, IsIntegral R (b i)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C),
      Module.Finite R C ∧ Algebra.FinitePresentation R C ∧
        ∃ g : C →ₐ[R] B, ∀ i, b i ∈ Set.range g := by
  induction n with
  | zero => exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance,
      Algebra.ofId R B, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨C, _, _, hCfin, hCfp, g, hg⟩ := ih (fun i ↦ b i.succ) (fun i ↦ hb i.succ)
    obtain ⟨p, hp, hpb⟩ := hb 0
    let q := p.map (algebraMap R C)
    let D := AdjoinRoot q
    have hDfin : Module.Finite C D := (hp.map (algebraMap R C)).finite_adjoinRoot
    have : Module.Finite R D := Module.Finite.trans C D
    have hroot : q.eval₂ g.toRingHom (b 0) = 0 := by
      dsimp [q]
      rw [Polynomial.eval₂_map, g.comp_algebraMap]
      exact hpb
    let g' : D →ₐ[R] B := AdjoinRoot.liftAlgHom q g (b 0) hroot
    refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, g', ?_⟩
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact ⟨AdjoinRoot.root q, AdjoinRoot.liftAlgHom_root q g (b 0) hroot⟩
    · obtain ⟨x, hx⟩ := hg j
      refine ⟨algebraMap C D x, ?_⟩
      change AdjoinRoot.liftAlgHom q g (b 0) hroot (AdjoinRoot.of q x) = b j.succ
      exact (AdjoinRoot.liftAlgHom_of q g (b 0) hroot x).trans hx

/-- 任意の有限 R-代数は、有限かつ有限表示の R-代数からの全射を受ける。 -/
theorem exists_finite_finitePresentation_surjective_model [Module.Finite R B] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C),
      Module.Finite R C ∧ Algebra.FinitePresentation R C ∧
        ∃ g : C →ₐ[R] B, Function.Surjective g := by
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := R) (M := B)
  obtain ⟨C, _, _, _, _, g, hg⟩ :=
    exists_finite_finitePresentation_model_of_integral_family (R := R)
    n b (fun i ↦ Algebra.IsIntegral.isIntegral (R := R) (b i))
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, g, ?_⟩
  apply (LinearMap.range_eq_top (f := g.toLinearMap)).mp
  apply top_unique
  rw [← hb]
  exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hg)

end SerrePositivity.AlgebraicGeometry
