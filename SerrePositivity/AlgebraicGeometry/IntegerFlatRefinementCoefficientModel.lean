module

public import SerrePositivity.AlgebraicGeometry.ProperSurjectiveCoefficientModel
public import SerrePositivity.AlgebraicGeometry.CoefficientSpecBaseNaturality
public import SerrePositivity.AlgebraicGeometry.IntegerFlatRefinementStage

/-!
概要：実際の固有全射と固定の整数平坦模型の細分を、共通の有限生成係数環へ降ろす。
方針：B01 の固有全射模型を供給し、同じ段への β と細分の射の因子化を適用する。
規約：元の環の Noether 性や模型の存在を追加仮定にしない。
使われ方：B02・B03 の実際の有限型係数被覆模型の供給。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 固有全射と固定の整数平坦模型の細分には、同じ係数段の実際の模型がある。 -/
theorem exists_integer_flat_refinement_coefficient_model
    (k R : Type u) [CommRing k] [IsNoetherianRing k] [CommRing R] [Algebra k R]
    {T Y Z V : Scheme.{u}} (r : T ⟶ Spec (CommRingCat.of R))
    [IsProper r] [LocallyOfFinitePresentation r] [Surjective r]
    (A : Type u) [CommRing A] [Algebra ℤ A] [Algebra.FiniteType ℤ A]
    (p : Y ⟶ Spec (CommRingCat.of A)) [LocallyOfFinitePresentation p]
    (q : Z ⟶ Y) [Flat q] [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q]
    (β : T ⟶ Y) [Surjective (pullback.snd q β)]
    (f : V ⟶ Spec (CommRingCat.of k)) [LocallyOfFinitePresentation f]
    (lInf : pullback q β ⟶ V)
    (hlInf : lInf ≫ f = pullback.snd q β ≫ r ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R))) :
    ∃ B : Subalgebra k R, B.FG ∧
      ∃ (Tj Wj : Scheme.{u}) (Rj : Tj ⟶ Spec (CommRingCat.of B)) (Qj : Wj ⟶ Tj)
        (l : Wj ⟶ V) (w : pullback q β ⟶ Wj),
        IsProper Rj ∧ LocallyOfFinitePresentation Rj ∧ Surjective Rj ∧
        Flat Qj ∧ LocallyOfFinitePresentation Qj ∧ QuasiCompact Qj ∧
        QuasiSeparated Qj ∧ Surjective Qj ∧
        l ≫ f = Qj ≫ Rj ≫ Spec.map (CommRingCat.ofHom (algebraMap k B)) ∧
        w ≫ l = lInf ∧ IsPullback w (pullback.snd q β ≫ r) (Qj ≫ Rj)
          (Spec.map (CommRingCat.ofHom (algebraMap B R))) := by
  obtain ⟨B₀, hB₀, T₀, r₀, hfp, hp, hs, a, hpb⟩ :=
    exists_proper_surjective_finitePresentation_coefficient_model k R r
  obtain ⟨s, rfl⟩ := hB₀
  letI := hfp
  letI := hp
  letI := hs
  let D := coefficientSpecDiagram k R
  let c := coefficientSpecCone k R
  have hc : IsLimit c := coefficientSpecConeIsLimit k R
  haveI (j : (Finset R)ᵒᵖ) : CompactSpace (D.obj j) := by
    dsimp [D, coefficientSpecDiagram]; infer_instance
  haveI (j : (Finset R)ᵒᵖ) : QuasiSeparatedSpace (D.obj j) := by
    dsimp [D, coefficientSpecDiagram]; infer_instance
  haveI {j m : (Finset R)ᵒᵖ} (g : j ⟶ m) : IsAffineHom (D.map g) := by
    dsimp [D, coefficientSpecDiagram]; infer_instance
  have hι : CommRingCat.ofHom (Algebra.adjoin k (s : Set R)).val.toRingHom =
      CommRingCat.ofHom (algebraMap (Algebra.adjoin k (s : Set R)) R) := by ext x; rfl
  have hpbc : IsPullback a r r₀ (c.π.app (.op s)) := by
    simpa only [c, coefficientSpecCone_projection, hι] using hpb
  obtain ⟨j, Tj, Wj, Rj, Qj, l, w, hR, hRfp, hRs, hQ, hQfp, hQqc, hQqs, hQs, hlf, hl, hcart⟩ :=
    exists_integer_flat_refinement_stage D c hc (.op s) a r r₀ hpbc A p q β
      (coefficientSpecBaseNatTrans k R) (Spec.map (CommRingCat.ofHom (algebraMap k R)))
      (coefficientSpecCone_base k R) f lInf hlInf
  let B := Algebra.adjoin k (j.unop : Set R)
  have hι' : CommRingCat.ofHom B.val.toRingHom = CommRingCat.ofHom (algebraMap B R) := by
    ext x
    rfl
  refine ⟨B, Subalgebra.fg_adjoin_finset j.unop, Tj, Wj, Rj, Qj, l, w,
    hR, hRfp, hRs, hQ, hQfp, hQqc, hQqs, hQs, hlf, hl, ?_⟩
  change IsPullback w (pullback.snd q β ≫ r) (Qj ≫ Rj)
    (Spec.map (CommRingCat.ofHom B.val.toRingHom)) at hcart
  simpa only [hι'] using hcart

end SerrePositivity.AlgebraicGeometry
