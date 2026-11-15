module

public import SerrePositivity.AlgebraicGeometry.IntegralProperClosedModel
public import SerrePositivity.AlgebraicGeometry.PullbackStageSurjectivity

/-!
概要：整射の実際の有限・有限表示段に、全射な固有閉部分の模型を取る。
方針：I04 上の閉部分模型に全射性の有限段の比較を適用し、Cartesian 性と周辺写像も保持する。
規約：一般の固有・局所有限表示の周辺模型。忠実平坦性は要求しない。
使われ方：A07 の固有側を同じ有限段へ移す接続。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 整射の実際のある有限・有限表示段で、固有閉部分模型を全射にする。 -/
theorem exists_surjective_proper_closed_integral_model
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] [Algebra.IsIntegral R B]
    (A : Type u) [CommRing A] [Algebra ℤ A] [Algebra.FiniteType ℤ A]
    (g : A →+* B) {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of A))
    [IsProper p] [LocallyOfFinitePresentation p]
    (K : (pullback p (Spec.map (CommRingCat.ofHom g))).IdealSheafData)
    (hK : IsFiniteTypeIdealSheaf K)
    [Surjective (K.subschemeι ≫ pullback.snd p (Spec.map (CommRingCat.ofHom g)))] :
    ∃ (i : IntegralModelIndex R B) (T : Scheme.{u})
      (r : T ⟶ (integralModelSpecDiagram R B).obj (.op i))
      (a : K.subscheme ⟶ T) (β : T ⟶ Y),
      IsProper r ∧ LocallyOfFinitePresentation r ∧ Surjective r ∧
      IsPullback a (K.subschemeι ≫ pullback.snd p (Spec.map (CommRingCat.ofHom g)))
        r ((integralModelSpecCone R B).π.app (.op i)) ∧
      a ≫ β = K.subschemeι ≫ pullback.fst p (Spec.map (CommRingCat.ofHom g)) := by
  let D := integralModelSpecDiagram R B
  let c := integralModelSpecCone R B
  have (i : (IntegralModelIndex R B)ᵒᵖ) : IsAffine (D.obj i) := by
    dsimp [D, integralModelSpecDiagram]
    infer_instance
  have {i j : (IntegralModelIndex R B)ᵒᵖ} (f : i ⟶ j) : IsAffineHom (D.map f) :=
    inferInstance
  obtain ⟨i, T, r, a, β, hr, hrfp, hpb, hβ⟩ :=
    exists_proper_closed_integral_model R B A g p K hK
  letI : IsProper r := hr
  letI : LocallyOfFinitePresentation r := hrfp
  obtain ⟨j, h, hsurj, a', hpb', ha'⟩ := exists_surjective_proper_stage_model D c
    (integralModelSpecConeIsLimit R B) a
    (K.subschemeι ≫ pullback.snd p (Spec.map (CommRingCat.ofHom g))) r hpb
  refine ⟨j.unop, pullback r (D.map h), pullback.snd r (D.map h), a',
    pullback.fst r (D.map h) ≫ β,
    MorphismProperty.pullback_snd (P := @IsProper) r (D.map h) hr,
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) r (D.map h) hrfp,
    hsurj, hpb', ?_⟩
  rw [← Category.assoc, ha']
  exact hβ

end SerrePositivity.AlgebraicGeometry
