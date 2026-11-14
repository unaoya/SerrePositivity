module

public import SerrePositivity.AlgebraicGeometry.CompositeStageBaseChangeLimit
public import SerrePositivity.AlgebraicGeometry.FinitePresentationClosedLimitModel

/-!
概要：因子化した係数写像の底変換上の有限型閉部分を、同じ基底の射影の底変換として降ろす。
方針：元の頂点を保つ極限 cone に C03 を適用し、二つの Cartesian な正方形を貼る。
規約：一般の固有・局所有限表示の周辺射。全射性は別の有限段の比較へ渡す。
使われ方：A07 の整射の有限表示段への閉包絡の移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 合成係数の底変換上の閉部分を、元の基底の同じ射影に関して Cartesian な固有模型へ降ろす。 -/
theorem exists_proper_closed_compositeStage_model
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : J) {S Y : Scheme.{u}} (γ : D.obj i ⟶ S) (p : Y ⟶ S)
    [IsProper p] [LocallyOfFinitePresentation p]
    (g : c.pt ⟶ S) (h : c.π.app i ≫ γ = g)
    (K : (pullback p g).IdealSheafData) (hK : IsFiniteTypeIdealSheaf K) :
    ∃ (j : Over i)
      (L : ((compositeStageBaseChangeDiagram D i γ p).obj j).IdealSheafData),
      IsFiniteTypeIdealSheaf L ∧
      IsProper (L.subschemeι ≫ pullback.fst (D.map j.hom ≫ γ) p) ∧
      LocallyOfFinitePresentation (L.subschemeι ≫ pullback.fst (D.map j.hom ≫ γ) p) ∧
      ∃ a : K.subscheme ⟶ L.subscheme,
        IsPullback a (K.subschemeι ≫ pullback.snd p g)
          (L.subschemeι ≫ pullback.fst (D.map j.hom ≫ γ) p) (c.π.app j.left) ∧
        a ≫ L.subschemeι ≫ pullback.snd (D.map j.hom ≫ γ) p =
          K.subschemeι ≫ pullback.fst p g := by
  let E := compositeStageBaseChangeDiagram D i γ p
  let C := compositeStageBaseChangeConeWithPoint D c i γ p g h
  obtain ⟨j, L, hL, hLfp, e, he⟩ := exists_finitePresentation_closed_model_of_isLimit E C
    (isLimit_compositeStageBaseChangeConeWithPoint D c hc i γ p g h) K hK
  letI : LocallyOfFinitePresentation L.subschemeι := hLfp
  haveI : IsProper (pullback.fst (D.map j.hom ≫ γ) p) :=
    MorphismProperty.pullback_fst (P := @IsProper) (D.map j.hom ≫ γ) p ‹IsProper p›
  haveI : LocallyOfFinitePresentation (pullback.fst (D.map j.hom ≫ γ) p) :=
    MorphismProperty.pullback_fst (P := @LocallyOfFinitePresentation)
      (D.map j.hom ≫ γ) p ‹LocallyOfFinitePresentation p›
  let a : K.subscheme ⟶ L.subscheme := e.hom ≫ pullback.snd (C.π.app j) L.subschemeι
  have hsq : K.subschemeι ≫ C.π.app j = a ≫ L.subschemeι := by
    rw [← he]
    simp only [a, Category.assoc, pullback.condition]
  have hclosed : IsPullback K.subschemeι a (C.π.app j) L.subschemeι :=
    IsPullback.of_iso_pullback ⟨hsq⟩ e he rfl
  refine ⟨j, L, hL, MorphismProperty.comp_mem _ _ _ inferInstance inferInstance,
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance, a, ?_, ?_⟩
  · exact hclosed.flip.paste_vert
      (isPullback_compositeStageBaseChangeConeWithPoint_π D c i γ p g h j)
  · rw [← Category.assoc, ← hsq, Category.assoc]
    exact congrArg (fun q ↦ K.subschemeι ≫ q)
      (compositeStageBaseChangeConeWithPoint_π_snd D c i γ p g h j)

end SerrePositivity.AlgebraicGeometry
