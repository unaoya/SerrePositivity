module

public import SerrePositivity.AlgebraicGeometry.AffineCartesianClosedLimit
public import SerrePositivity.AlgebraicGeometry.ClosedPullbackComposite
public import SerrePositivity.AlgebraicGeometry.FlatStageModelLimit

/-!
概要：一般の標的上の affine な射を、一つの affine な標的へ制限して閉埋め込み性を降ろす。
方針：標的の制限と源の二段の実際の底変換の極限に、affine Cartesian な極限の補題を使う。
規約：Noether 性・固有性・開包含はこの局所的な接続では仮定しない。
使われ方：C04 の有限 affine 被覆の各制限での閉埋め込み性の有限段への降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- affine な標的への制限の、極限での閉埋め込み性をある後段へ降ろす。 -/
theorem exists_closedImmersion_restricted_stage
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {j k} (a : j ⟶ k), IsAffineHom (D.map a)]
    {i : J} {X V : Scheme.{u}} [IsAffine V]
    (f : X ⟶ D.obj i) [IsAffineHom f] [LocallyOfFiniteType f]
    (r : V ⟶ D.obj i) [IsClosedImmersion (pullback.snd f (c.π.app i))] :
    ∃ j : Over i, IsClosedImmersion
      ((flatStageModelProjection D i r r f).app j) := by
  let a := pullback.fst r (c.π.app i)
  let x := pullback.snd r (c.π.app i)
  have hpb : IsPullback a x r (c.π.app i) := IsPullback.of_hasPullback r (c.π.app i)
  let b := a ≫ r
  let B := stageBaseChangeDiagram D i r
  let E := flatStageModelDiagram D i r r f
  let cb := stageModelCone D c i a x r hpb
  let ce := flatStageModelConeWithPoint D c i a x r hpb r f b rfl
  let τ := flatStageModelProjection D i r r f
  haveI (j : Over i) : IsAffine (B.obj j) := by dsimp [B, stageBaseChangeDiagram]; infer_instance
  haveI (j : Over i) : IsAffine (E.obj j) := by dsimp [E, flatStageModelDiagram]; infer_instance
  haveI : IsClosedImmersion (pullback.snd f b) :=
    isClosedImmersion_pullback_snd_of_composite f (c.π.app i) x b
      (pullback.condition.symm)
  let o : Over i := Over.mk (𝟙 i)
  haveI : LocallyOfFiniteType (τ.app o) := by
    dsimp [τ, flatStageModelProjection]
    infer_instance
  obtain ⟨j, _, hj⟩ := exists_closedImmersion_stage_of_affine_cartesian_limit B E τ cb ce
    (isLimit_stageModelCone D c hc i a x r hpb)
    (isLimit_flatStageModelConeWithPoint D c hc i a x r hpb r f b rfl)
    (pullback.snd f b)
    (fun j ↦ flatStageModelConeWithPoint_π_fst D c i a x r hpb r f b rfl j)
    o (fun j k ↦ isPullback_flatStageModelDiagram_map D i r r f k)
  exact ⟨j, hj⟩

/-- 有限個の affine な標的への制限の閉埋め込み性を同じ後段へそろえる。 -/
theorem exists_finite_closedImmersion_restricted_stage
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {j k} (a : j ⟶ k), IsAffineHom (D.map a)]
    {i : J} {X : Scheme.{u}} (f : X ⟶ D.obj i)
    [IsAffineHom f] [LocallyOfFiniteType f]
    [IsClosedImmersion (pullback.snd f (c.π.app i))]
    {ι : Type u} [Finite ι] (V : ι → Scheme.{u}) [∀ a, IsAffine (V a)]
    (r : ∀ a, V a ⟶ D.obj i) :
    ∃ j : Over i, ∀ a, IsClosedImmersion
      ((flatStageModelProjection D i (r a) (r a) f).app j) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  choose j hj using fun a ↦ exists_closedImmersion_restricted_stage D c hc f (r a)
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  let q (a : ι) : k ⟶ j a := (hk (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)).some
  refine ⟨k, fun a ↦ ?_⟩
  exact MorphismProperty.of_isPullback
    (isPullback_flatStageModelDiagram_map D i (r a) (r a) f (q a)) (hj a)

end SerrePositivity.AlgebraicGeometry
