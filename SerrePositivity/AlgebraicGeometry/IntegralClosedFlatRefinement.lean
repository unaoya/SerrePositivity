module

public import SerrePositivity.AlgebraicGeometry.FlatStageModelFactorization
public import SerrePositivity.AlgebraicGeometry.IntegralModelBaseNaturality
public import SerrePositivity.AlgebraicGeometry.IntegralSurjectiveProperClosedModel

/-!
概要：整全射のある有限・有限表示段で、実際の閉部分の固有模型と平坦模型を合成する。
方針：固有側の全射な模型、平坦側の全射な段での因子化、I04 の基底への有限全射を使う。
規約：入力の模型は呼出側で実際に供給する。この接続だけで一般の細分の完成とはしない。
使われ方：A07 の C01 の整拡大後の Noether 平坦模型を元の基底へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 整全射後の閉部分と平坦模型の証人を、元の基底上の実際の fppf–proper 細分へ合成する。 -/
theorem exists_fppf_proper_refinement_of_integral_closed_flat_model
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] [Algebra.IsIntegral R B]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    (A : Type u) [CommRing A] [Algebra ℤ A] [Algebra.FiniteType ℤ A]
    (g : A →+* B) {Y Z V : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of A))
    [IsProper p] [LocallyOfFinitePresentation p] (q : Z ⟶ Y)
    [Flat q] [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q]
    (K : (pullback p (Spec.map (CommRingCat.ofHom g))).IdealSheafData)
    (hK : IsFiniteTypeIdealSheaf K)
    [Surjective (K.subschemeι ≫ pullback.snd p (Spec.map (CommRingCat.ofHom g)))]
    [Surjective (pullback.snd q (K.subschemeι ≫ pullback.fst p (Spec.map (CommRingCat.ofHom g))))]
    (f : V ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation f]
    (lInf : pullback q (K.subschemeι ≫ pullback.fst p (Spec.map (CommRingCat.ofHom g))) ⟶ V)
    (hlInf : lInf ≫ f = pullback.snd _ _ ≫ K.subschemeι ≫
      pullback.snd p (Spec.map (CommRingCat.ofHom g)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    ∃ (T W : Scheme.{u}) (q' : W ⟶ T) (r' : T ⟶ Spec (CommRingCat.of R)) (l : W ⟶ V),
      IsProper r' ∧ LocallyOfFinitePresentation r' ∧ Surjective r' ∧ Flat q' ∧
      LocallyOfFinitePresentation q' ∧ QuasiCompact q' ∧ Surjective q' ∧ l ≫ f = q' ≫ r' := by
  let D := integralModelSpecDiagram R B
  let c := integralModelSpecCone R B
  have (i : (IntegralModelIndex R B)ᵒᵖ) : IsAffine (D.obj i) := by
    dsimp [D, integralModelSpecDiagram]
    infer_instance
  have {i j : (IntegralModelIndex R B)ᵒᵖ} (h : i ⟶ j) : IsAffineHom (D.map h) :=
    inferInstance
  obtain ⟨i, T, r, a, β, hr, hrfp, hrsurj, hpb, hβ⟩ :=
    exists_surjective_proper_closed_integral_model R B A g p K hK
  letI : IsProper r := hr
  letI : LocallyOfFinitePresentation r := hrfp
  letI : Surjective r := hrsurj
  obtain ⟨j, l, hqsurj, hl, hlf⟩ := exists_surjective_flat_stage_factor D c
    (integralModelSpecConeIsLimit R B) (.op i) a
    (K.subschemeι ≫ pullback.snd p (Spec.map (CommRingCat.ofHom g))) r hpb β q
    (K.subschemeι ≫ pullback.fst p (Spec.map (CommRingCat.ofHom g))) hβ
    (integralModelSpecBaseNatTrans R B)
    (Spec.map (CommRingCat.ofHom (algebraMap R B))) (integralModelSpecCone_base R B)
    f lInf (by simpa only [Category.assoc] using hlInf)
  let rj := pullback.fst (D.map j.hom) r
  let base := integralModelSpecBaseMap R B j.left.unop
  haveI : IsProper rj := MorphismProperty.pullback_fst _ r hr
  haveI : LocallyOfFinitePresentation rj := MorphismProperty.pullback_fst _ r hrfp
  haveI : Surjective rj := MorphismProperty.pullback_fst _ r hrsurj
  haveI : Surjective base := integralModelSpecBaseMap_surjective R B j.left.unop
  let qj := (flatStageModelProjection D (.op i) r β q).app j
  refine ⟨(stageBaseChangeDiagram D (.op i) r).obj j,
    (flatStageModelDiagram D (.op i) r β q).obj j, qj, rj ≫ base, l,
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance,
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance,
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance,
    inferInstance, inferInstance, inferInstance, hqsurj, ?_⟩
  simpa only [flatStageModelBaseMap, stageModelBaseMap, NatTrans.comp_app,
    integralModelSpecBaseNatTrans, qj, rj, base, Category.assoc] using hlf

end SerrePositivity.AlgebraicGeometry
