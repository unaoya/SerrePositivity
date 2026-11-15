module

public import SerrePositivity.AlgebraicGeometry.FlatStageModelSurjective
public import SerrePositivity.AlgebraicGeometry.FlatStageModelBase

/-!
概要：全射となった平坦模型の段より後で、元の S 上の射を因子化する。
方針：全射な段の Over へ制限し、既存の局所有限表示射の因子化を使う。
規約：型と基底上の可換式を保持する。導来・Čech の比較には触れない。
使われ方：A07 の元の X への因子化を全射性と同じ段へそろえる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- ある全射な平坦模型の実際の段で、元の被覆からの S 上の射を因子化する。 -/
theorem exists_surjective_flat_stage_factor
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : J) {X T Y Z S V : Scheme.{u}} (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) [QuasiCompact r] [QuasiSeparated r]
    (β : T ⟶ Y) (q : Z ⟶ Y) [Flat q] [LocallyOfFinitePresentation q]
    [QuasiCompact q] [QuasiSeparated q] (b : X ⟶ Y) (hb : a ≫ β = b)
    [Surjective (pullback.snd q b)] (t : D ⟶ (Functor.const J).obj S)
    (s : c.pt ⟶ S) (hs : ∀ j, c.π.app j ≫ t.app j = s)
    (f : V ⟶ S) [LocallyOfFinitePresentation f] (lInf : pullback q b ⟶ V)
    (hlInf : lInf ≫ f = pullback.snd q b ≫ x ≫ s) :
    ∃ (j : Over i) (l : (flatStageModelDiagram D i r β q).obj j ⟶ V),
      Surjective ((flatStageModelProjection D i r β q).app j) ∧
      (flatStageModelConeWithPoint D c i a x r hpb β q b hb).π.app j ≫ l = lInf ∧
      l ≫ f = (flatStageModelBaseMap D i r β q t).app j := by
  let W := flatStageModelDiagram D i r β q
  let C := flatStageModelConeWithPoint D c i a x r hpb β q b hb
  let Q := flatStageModelProjection D i r β q
  let u := flatStageModelBaseMap D i r β q t
  have hC : IsLimit C := isLimit_flatStageModelConeWithPoint D c hc i a x r hpb β q b hb
  obtain ⟨j, hj⟩ := exists_surjective_flat_stage_of_model D c hc i a x r hpb β q b hb
  letI : Surjective (Q.app j) := hj
  let E : Over j ⥤ Scheme.{u} := Over.forget j ⋙ W
  have {k l : Over j} (g : k ⟶ l) : IsAffineHom (E.map g) := by
    change IsAffineHom ((flatStageModelDiagram D i r β q).map g.left)
    infer_instance
  have (k : Over j) : CompactSpace (E.obj k) :=
    inferInstanceAs (CompactSpace ((flatStageModelDiagram D i r β q).obj k.left))
  have (k : Over j) : QuasiSeparatedSpace (E.obj k) :=
    inferInstanceAs (QuasiSeparatedSpace ((flatStageModelDiagram D i r β q).obj k.left))
  let C' : Cone E := C.whisker (Over.forget j)
  have hC' : IsLimit C' := (Functor.Initial.isLimitWhiskerEquiv (Over.forget j) C).symm hC
  let u' : E ⟶ (Functor.const (Over j)).obj S := Functor.whiskerLeft (Over.forget j) u
  have htriangle : C'.π ≫ u' = (Functor.const (Over j)).map (lInf ≫ f) := by
    ext k
    change C.π.app k.left ≫ u.app k.left = lInf ≫ f
    rw [hlInf]
    exact flatStageModelConeWithPoint_π_base D c i a x r hpb β q b hb t s hs k.left
  obtain ⟨k, l, hl, hlf⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    E u' f C' hC' lInf htriangle
  refine ⟨k.left, l, ?_, hl, hlf⟩
  exact surjective_component_of_cartesian_model_map Q k.hom
    (isPullback_flatStageModelDiagram_map D i r β q k.hom)

end SerrePositivity.AlgebraicGeometry
