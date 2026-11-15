module

public import SerrePositivity.AlgebraicGeometry.IntegerModelStageFactor
public import SerrePositivity.AlgebraicGeometry.FlatStageModelFactorization

/-!
概要：固定の整数平坦模型と、細分の射・全射性を同じ実際の有限段へそろえる。
方針：β を因子化し、その段で既存の平坦模型の全射性と射の因子化を適用する。
規約：固有側・平坦側の性質と元の対象との Cartesian 比較を保つ。
使われ方：B02・B03 の有限係数段上の v 被覆性の証明。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 固有模型と固定の整数平坦模型の細分は、同じ実際の有限段へ降りる。 -/
theorem exists_integer_flat_refinement_stage
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {j k} (a : j ⟶ k), IsAffineHom (D.map a)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (i : J) {T T₀ Y Z S V : Scheme.{u}}
    (a : T ⟶ T₀) (x : T ⟶ c.pt) (r : T₀ ⟶ D.obj i)
    [IsProper r] [LocallyOfFinitePresentation r] [Surjective r]
    (hpb : IsPullback a x r (c.π.app i))
    (A : Type u) [CommRing A] [Algebra ℤ A] [Algebra.FiniteType ℤ A]
    (p : Y ⟶ Spec (CommRingCat.of A)) [LocallyOfFinitePresentation p]
    (q : Z ⟶ Y) [Flat q] [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q]
    (β : T ⟶ Y) [Surjective (pullback.snd q β)]
    (u : D ⟶ (Functor.const J).obj S) (s : c.pt ⟶ S)
    (hs : ∀ j, c.π.app j ≫ u.app j = s)
    (f : V ⟶ S) [LocallyOfFinitePresentation f] (lInf : pullback q β ⟶ V)
    (hlInf : lInf ≫ f = pullback.snd q β ≫ x ≫ s) :
    ∃ (j : J) (Tj Wj : Scheme.{u}) (Rj : Tj ⟶ D.obj j) (Qj : Wj ⟶ Tj)
      (l : Wj ⟶ V) (w : pullback q β ⟶ Wj),
      IsProper Rj ∧ LocallyOfFinitePresentation Rj ∧ Surjective Rj ∧
      Flat Qj ∧ LocallyOfFinitePresentation Qj ∧ QuasiCompact Qj ∧
      QuasiSeparated Qj ∧ Surjective Qj ∧ l ≫ f = Qj ≫ Rj ≫ u.app j ∧
      w ≫ l = lInf ∧ IsPullback w (pullback.snd q β ≫ x) (Qj ≫ Rj) (c.π.app j) := by
  obtain ⟨j, b, hb⟩ := exists_integerModel_stage_factor D c hc i a x r hpb A p β
  let aj := (stageModelCone D c i a x r hpb).π.app j
  let rj : (stageBaseChangeDiagram D i r).obj j ⟶ D.obj j.left :=
    pullback.fst (D.map j.hom) r
  have hpbj : IsPullback aj x rj (c.π.app j.left) :=
    isPullback_stageModelCone_π D c i a x r hpb j
  haveI : IsProper rj := by dsimp [rj]; infer_instance
  haveI : LocallyOfFinitePresentation rj := by dsimp [rj]; infer_instance
  haveI : Surjective rj := by dsimp [rj]; infer_instance
  obtain ⟨k, l, hq, hl, hlf⟩ := exists_surjective_flat_stage_factor
    D c hc j.left aj x rj hpbj b q β hb u s hs f lInf hlInf
  let Rj := pullback.fst (D.map k.hom) rj
  let Qj := (flatStageModelProjection D j.left rj b q).app k
  let w := (flatStageModelConeWithPoint D c j.left aj x rj hpbj b q β hb).π.app k
  have hR : IsPullback ((stageModelCone D c j.left aj x rj hpbj).π.app k)
      x Rj (c.π.app k.left) := isPullback_stageModelCone_π D c j.left aj x rj hpbj k
  have hQ : IsPullback w (pullback.snd q β) Qj
      ((stageModelCone D c j.left aj x rj hpbj).π.app k) :=
    isPullback_flatStageModelConeWithPoint_π D c j.left aj x rj hpbj b q β hb k
  refine ⟨k.left, (stageBaseChangeDiagram D j.left rj).obj k,
    (flatStageModelDiagram D j.left rj b q).obj k, Rj, Qj, l, w,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hq, ?_, hl, hQ.paste_vert hR⟩
  simpa only [flatStageModelBaseMap, stageModelBaseMap, NatTrans.comp_app,
    Qj, Rj, Category.assoc] using hlf

end SerrePositivity.AlgebraicGeometry
