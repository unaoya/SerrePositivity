module

public import SerrePositivity.AlgebraicGeometry.ProperFinitePresentationCoefficientModel
public import SerrePositivity.AlgebraicGeometry.ProperFinitePresentationSurjectivityLimit

/-!
概要：固有全射な局所有限表示対象を、実際の有限生成係数部分代数へ降ろす。
方針：実際の固有模型を作り、既存の全射性の有限段への降下を適用する。
規約：元の環の Noether 性や全射な模型の存在を仮定しない。
使われ方：B02 の固有性・全射性を同じ有限段へそろえる接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v

/-- 一般の固有全射・有限表示射の、同じ係数段上の実際の固有全射模型。 -/
theorem exists_proper_surjective_finitePresentation_coefficient_model
    (k : Type v) (R : Type u) [CommRing k] [IsNoetherianRing k] [CommRing R] [Algebra k R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation f] [IsProper f] [Surjective f] :
    ∃ (A : Subalgebra k R), A.FG ∧ ∃ (Y : Scheme.{u}) (p : Y ⟶ Spec (CommRingCat.of A)),
      LocallyOfFinitePresentation p ∧ IsProper p ∧ Surjective p ∧
        ∃ a : X ⟶ Y, IsPullback a f p (Spec.map (CommRingCat.ofHom (algebraMap A R))) := by
  obtain ⟨A, hA, Y, p, hfp, hproper, a, hpb⟩ := exists_proper_finitePresentation_coefficient_model k R f
  obtain ⟨s, rfl⟩ := hA
  letI := hfp
  letI := hproper
  let D := coefficientSpecDiagram k R
  let c := coefficientSpecCone k R
  have hc : IsLimit c := coefficientSpecConeIsLimit k R
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
  haveI : Surjective (pullback.snd p (c.π.app (.op s))) := by
    have H : Surjective (hpbc.isoPullback.inv ≫ f) := inferInstance
    simpa only [IsPullback.isoPullback_inv_snd] using H
  obtain ⟨j, g, hj⟩ := exists_surjective_proper_pullback_of_isLimit D hc (i := .op s) p
  let B := Algebra.adjoin k (j.unop : Set R)
  let Y' := pullback p (D.map g)
  let p' := pullback.snd p (D.map g)
  letI : Surjective p' := hj
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
  refine ⟨B, Subalgebra.fg_adjoin_finset j.unop, Y', p', inferInstance, inferInstance,
    inferInstance, a', ?_⟩
  change IsPullback a' f p' (Spec.map (CommRingCat.ofHom B.val.toRingHom)) at hpb'
  simpa only [hι'] using hpb'

end SerrePositivity.AlgebraicGeometry
