module

public import SerrePositivity.AlgebraicGeometry.IntegralClosedFlatRefinement

/-!
概要：整全射後の実際の細分から、固定の平坦模型の証人を保持する。
方針：既存の同じ段を取り、二段の底変換を標準の pullback へ同型で戻す。
規約：入力の模型は呼出側で実際に供給する。この接続だけで一般の細分の完成とはしない。
使われ方：B03 の G1 で構成した平坦な証人の実際のモデル化。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 整全射後の実際の細分で、元の固定の平坦模型とその底変換を保持する。 -/
theorem exists_proper_flat_model_witness_of_integral_closed_model
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
    ∃ (T : Scheme.{u}) (r' : T ⟶ Spec (CommRingCat.of R)) (β' : T ⟶ Y),
      IsProper r' ∧ LocallyOfFinitePresentation r' ∧ Surjective r' ∧
      Surjective (pullback.snd q β') ∧
      ∃ l : pullback q β' ⟶ V, l ≫ f = pullback.snd q β' ≫ r' := by
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
  let βj := pullback.snd (D.map j.hom) r ≫ β
  let qj : pullback βj q ⟶ pullback (D.map j.hom) r :=
    (flatStageModelProjection D (.op i) r β q).app j
  let lj : pullback βj q ⟶ V := l
  let E := pullbackSymmetry q βj
  let m := E.hom ≫ lj
  letI : Surjective qj := hqsurj
  have he : E.hom ≫ qj = pullback.snd q βj := by
    exact pullbackSymmetry_hom_comp_fst q βj
  have hs : Surjective (pullback.snd q βj) := by
    have H : Surjective (E.hom ≫ qj) := inferInstance
    simpa only [he] using H
  have hlf' : lj ≫ f = qj ≫ rj ≫ base := by
    simpa only [flatStageModelBaseMap, stageModelBaseMap, NatTrans.comp_app,
      integralModelSpecBaseNatTrans, qj, rj, base, Category.assoc] using hlf
  refine ⟨pullback (D.map j.hom) r, rj ≫ base, βj,
    inferInstance, inferInstance, inferInstance, hs, m, ?_⟩
  dsimp only [m]
  rw [Category.assoc, hlf', ← Category.assoc E.hom qj, he]

end SerrePositivity.AlgebraicGeometry
