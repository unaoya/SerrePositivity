module

public import SerrePositivity.AlgebraicGeometry.StageBaseChangeLimit
public import SerrePositivity.AlgebraicGeometry.FinitePresentationClosedLimitModel

/-!
概要：固有・局所有限表示の周辺空間の底変換上の有限型閉部分を有限段へ降ろす。
方針：実際の底変換図式に C03 を適用し、閉包含と固有射の合成を使う。
規約：全射性はこの補題の結論に含めない。忠実平坦性は要求しない。
使われ方：A07 の整拡大後の閉包絡の有限・有限表示段への移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 固有な周辺模型の極限への底変換上の有限型閉部分は、固有・局所有限表示の有限段の模型を持つ。 -/
theorem exists_proper_closed_baseChange_model_of_isLimit
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : J) {Y : Scheme.{u}} (p : Y ⟶ D.obj i)
    [IsProper p] [LocallyOfFinitePresentation p]
    (K : (pullback (c.π.app i) p).IdealSheafData) (hK : IsFiniteTypeIdealSheaf K) :
    ∃ (j : Over i) (L : ((stageBaseChangeDiagram D i p).obj j).IdealSheafData),
      IsFiniteTypeIdealSheaf L ∧
      IsProper (L.subschemeι ≫ pullback.fst (D.map j.hom) p) ∧
      LocallyOfFinitePresentation (L.subschemeι ≫ pullback.fst (D.map j.hom) p) ∧
      ∃ e : K.subscheme ≅ pullback ((stageBaseChangeCone D c i p).π.app j) L.subschemeι,
        e.hom ≫ pullback.fst _ _ = K.subschemeι := by
  obtain ⟨j, L, hL, hLfp, e, he⟩ :=
    exists_finitePresentation_closed_model_of_isLimit (stageBaseChangeDiagram D i p)
      (stageBaseChangeCone D c i p) (isLimit_stageBaseChangeCone D c hc i p) K hK
  letI : LocallyOfFinitePresentation L.subschemeι := hLfp
  haveI : IsProper (pullback.fst (D.map j.hom) p) :=
    MorphismProperty.pullback_fst (P := @IsProper) (D.map j.hom) p ‹IsProper p›
  haveI : LocallyOfFinitePresentation (pullback.fst (D.map j.hom) p) :=
    MorphismProperty.pullback_fst (P := @LocallyOfFinitePresentation) (D.map j.hom) p
      ‹LocallyOfFinitePresentation p›
  exact ⟨j, L, hL, MorphismProperty.comp_mem _ _ _ inferInstance inferInstance,
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance, e, he⟩

end SerrePositivity.AlgebraicGeometry
