module

public import SerrePositivity.AlgebraicGeometry.SeparatedFinitePresentationCoefficientModel
public import SerrePositivity.AlgebraicGeometry.NoetherianProperLimitDescent

/-!
概要：固有な局所有限表示対象を、実際の有限生成係数部分代数へ降ろす。
方針：分離的な実際の係数模型を作り、Chow の支配で固有性を後段へ降ろす。
規約：元の環の Noether 性や固有な模型の存在を仮定しない。
使われ方：B01 の一般の固有模型の供給。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v

/-- 一般の固有・有限表示対象の、有限生成係数部分代数上の実際の固有な模型。 -/
theorem exists_proper_finitePresentation_coefficient_model
    (k : Type v) (R : Type u) [CommRing k] [IsNoetherianRing k] [CommRing R] [Algebra k R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation f] [IsProper f] :
    ∃ (A : Subalgebra k R), A.FG ∧ ∃ (Y : Scheme.{u}) (p : Y ⟶ Spec (CommRingCat.of A)),
      LocallyOfFinitePresentation p ∧ IsProper p ∧
        ∃ a : X ⟶ Y, IsPullback a f p (Spec.map (CommRingCat.ofHom (algebraMap A R))) := by
  obtain ⟨A, hA, Y, p, hfp, hq, hs, hsep, a, hpb⟩ :=
    exists_separated_finitePresentation_coefficient_model k R f
  obtain ⟨s, rfl⟩ := hA
  letI := hfp
  letI := hq
  letI := hs
  letI := hsep
  letI : IsNoetherianRing (Algebra.adjoin k (s : Set R)) :=
    isNoetherianRing_of_fg (Subalgebra.fg_adjoin_finset s)
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  letI : IsNoetherian Y := ⟨⟩
  let D := coefficientSpecDiagram k R
  let c := coefficientSpecCone k R
  have hc : IsLimit c := coefficientSpecConeIsLimit k R
  haveI : IsAffine (D.obj (.op s)) := by
    dsimp [D, coefficientSpecDiagram]
    infer_instance
  haveI (j : (Finset R)ᵒᵖ) : CompactSpace (D.obj j) := by
    dsimp [D, coefficientSpecDiagram]; infer_instance
  haveI (j : (Finset R)ᵒᵖ) : QuasiSeparatedSpace (D.obj j) := by
    dsimp [D, coefficientSpecDiagram]; infer_instance
  haveI {j l : (Finset R)ᵒᵖ} (g : j ⟶ l) : IsAffineHom (D.map g) := by
    dsimp [D, coefficientSpecDiagram]; infer_instance
  have hι : CommRingCat.ofHom (Algebra.adjoin k (s : Set R)).val.toRingHom =
      CommRingCat.ofHom (algebraMap (Algebra.adjoin k (s : Set R)) R) := by ext x; rfl
  have hpbc : IsPullback a f p (c.π.app (.op s)) := by
    simpa only [c, coefficientSpecCone_projection, hι] using hpb
  haveI : IsProper (pullback.snd p (c.π.app (.op s))) := by
    have H : IsProper (hpbc.isoPullback.inv ≫ f) := inferInstance
    simpa only [IsPullback.isoPullback_inv_snd] using H
  obtain ⟨j, g, hj⟩ := exists_isProper_pullback_of_isLimit_of_noetherian_source D c hc (i := .op s) p
  let B := Algebra.adjoin k (j.unop : Set R)
  let Y' := pullback p (D.map g)
  let p' := pullback.snd p (D.map g)
  letI : IsProper p' := hj
  let a' : X ⟶ Y' := pullback.lift a (f ≫ c.π.app j) (by
    rw [Category.assoc, c.w]
    exact hpbc.w)
  have hw : c.π.app j ≫ D.map g = c.π.app (.op s) := by
    simpa only [Functor.const_obj_map, Category.id_comp] using c.w g
  have hpb' : IsPullback a' f p' (c.π.app j) := by
    apply IsPullback.of_right ?_ (by simp [a', p']) (IsPullback.of_hasPullback p (D.map g))
    simpa only [a', pullback.lift_fst, hw] using hpbc
  have hι' : CommRingCat.ofHom B.val.toRingHom = CommRingCat.ofHom (algebraMap B R) := by
    ext x
    rfl
  refine ⟨B, Subalgebra.fg_adjoin_finset j.unop, Y', p', inferInstance, inferInstance, a', ?_⟩
  change IsPullback a' f p' (Spec.map (CommRingCat.ofHom B.val.toRingHom)) at hpb'
  simpa only [hι'] using hpb'

end SerrePositivity.AlgebraicGeometry
