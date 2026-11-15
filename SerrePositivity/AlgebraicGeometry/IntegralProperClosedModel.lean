module

public import SerrePositivity.AlgebraicGeometry.ProperClosedCompositeStageModel
public import SerrePositivity.AlgebraicGeometry.IntegralModelCoefficientFactor

/-!
概要：整射の実際の有限・有限表示段へ、Noether 周辺模型上の閉部分を降ろす。
方針：I03 の係数因子化、I04 の Spec の極限、C03 の同じ基底に関する閉部分模型を合成する。
規約：整射の単射性・忠実平坦性を仮定しない。全射性は後続の有限段の比較に渡す。
使われ方：A07 の実際の閉包絡の有限段への移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 整射の実際の有限・有限表示段に、閉部分の固有・局所有限表示模型と周辺模型への射を取る。 -/
theorem exists_proper_closed_integral_model
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] [Algebra.IsIntegral R B]
    (A : Type u) [CommRing A] [Algebra ℤ A] [Algebra.FiniteType ℤ A]
    (g : A →+* B) {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of A))
    [IsProper p] [LocallyOfFinitePresentation p]
    (K : (pullback p (Spec.map (CommRingCat.ofHom g))).IdealSheafData)
    (hK : IsFiniteTypeIdealSheaf K) :
    ∃ (i : IntegralModelIndex R B) (T : Scheme.{u})
      (r : T ⟶ (integralModelSpecDiagram R B).obj (.op i))
      (a : K.subscheme ⟶ T) (β : T ⟶ Y),
      IsProper r ∧ LocallyOfFinitePresentation r ∧
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
  obtain ⟨i, γ, hγ⟩ := exists_integral_model_spec_factor_of_finiteType_int R B A g
  obtain ⟨j, L, hL, hr, hrfp, a, hpb, hβ⟩ :=
    exists_proper_closed_compositeStage_model D c (integralModelSpecConeIsLimit R B)
      (.op i) γ p (Spec.map (CommRingCat.ofHom g)) hγ K hK
  exact ⟨j.left.unop, L.subscheme, _, a, _, hr, hrfp, hpb, hβ⟩

end SerrePositivity.AlgebraicGeometry
