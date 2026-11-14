module

public import SerrePositivity.AlgebraicGeometry.PullbackStageSurjectivity

/-!
概要：Cartesian な模型の図式の、実際の平坦な成分をある段で全射にする。
方針：固定した成分の全射性を有限段へ移し、Cartesian な遷移の比較同型で実際の成分へ戻す。
規約：既存の全射性の有限段への移送と底変換の法則。忠実平坦性は要求しない。
使われ方：A07 の実際の W_j→T_j を全射にする。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 全射になった成分より後の実際の成分も、Cartesian な底変換で全射。 -/
theorem surjective_component_of_cartesian_model_map
    {J : Type u} [SmallCategory J] {W D : J ⥤ Scheme.{u}} (q : W ⟶ D)
    {j i : J} (f : j ⟶ i)
    (h : IsPullback (W.map f) (q.app j) (q.app i) (D.map f))
    [Surjective (q.app i)] : Surjective (q.app j) :=
  MorphismProperty.of_isPullback h inferInstance

/-- 極限上の全射な平坦模型を、ある段の実際の成分の全射性へ渡す。 -/
theorem exists_surjective_component_of_cartesian_flat_model
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] (W : J ⥤ Scheme.{u}) (q : W ⟶ D)
    [∀ i, Flat (q.app i)] [∀ i, LocallyOfFinitePresentation (q.app i)]
    [∀ i, QuasiCompact (q.app i)]
    (hcart : ∀ {j i} (f : j ⟶ i), IsPullback (W.map f) (q.app j) (q.app i) (D.map f))
    {X : Scheme.{u}} (x : X ⟶ c.pt) [Surjective x]
    (w : ∀ i, X ⟶ W.obj i) (hw : ∀ i, IsPullback (w i) x (q.app i) (c.π.app i)) :
    ∃ j, Surjective (q.app j) := by
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := J)
  obtain ⟨j, f, hs, _⟩ := exists_surjective_flat_stage_model D c hc (w i) x (q.app i) (hw i)
  let h := hcart f
  haveI : Surjective (pullback.snd (q.app i) (D.map f)) := hs
  haveI : Surjective (h.isoPullback.hom) := inferInstance
  have hs' : Surjective (h.isoPullback.hom ≫ pullback.snd (q.app i) (D.map f)) := inferInstance
  exact ⟨j, by simpa only [h.isoPullback_hom_snd] using hs'⟩

end SerrePositivity.AlgebraicGeometry
