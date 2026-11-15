module

public import SerrePositivity.AlgebraicGeometry.ProperFinitePresentationSurjectivityLimit
public import SerrePositivity.AlgebraicGeometry.FlatSurjectivityLimit

/-!
概要：全射性が得られる有限段で、元の模型からの実際の射と Cartesian 性も保持する。
方針：pullback の比較同型で全射性を検出し、後段への pullback.lift と正方形の貼り合わせを使う。
規約：固有側・平坦側の既存の有限段の比較の法則。忠実平坦性は要求しない。
使われ方：A07 で模型の全射性・因子化を同じ段にそろえる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

private theorem stage_surjective_pullback_snd
    {X T B S : Scheme.{u}} {a : X ⟶ T} {x : X ⟶ B} {r : T ⟶ S} {g : B ⟶ S}
    (hpb : IsPullback a x r g) [Surjective x] : Surjective (pullback.snd r g) := by
  haveI : Surjective (hpb.isoPullback.hom ≫ pullback.snd r g) := by
    rw [hpb.isoPullback_hom_snd]
    infer_instance
  exact Surjective.of_comp (f := hpb.isoPullback.hom) (g := pullback.snd r g)

set_option backward.isDefEq.respectTransparency false in
private theorem stage_model_map_of_isPullback
    {J : Type u} [SmallCategory J] (D : J ⥤ Scheme.{u}) (c : Cone D)
    {i j : J} (h : j ⟶ i) {X T : Scheme.{u}} (a : X ⟶ T)
    (x : X ⟶ c.pt) (r : T ⟶ D.obj i) (hpb : IsPullback a x r (c.π.app i)) :
    ∃ a' : X ⟶ pullback r (D.map h),
      IsPullback a' x (pullback.snd r (D.map h)) (c.π.app j) ∧
      a' ≫ pullback.fst r (D.map h) = a := by
  let a' : X ⟶ pullback r (D.map h) :=
    pullback.lift a (x ≫ c.π.app j) (by rw [Category.assoc, c.w]; exact hpb.w)
  have houter : IsPullback (a' ≫ pullback.fst r (D.map h)) x r
      (c.π.app j ≫ D.map h) := by
    simpa only [a', pullback.lift_fst, c.w] using hpb
  refine ⟨a', houter.of_right ?_ (IsPullback.of_hasPullback r (D.map h)), ?_⟩
  · simp [a']
  · simp [a']

/-- 固有な模型の全射性が降りる段で、同じ模型の実際の射と Cartesian 性を保持する。 -/
theorem exists_surjective_proper_stage_model
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {i : J} {X T : Scheme.{u}} (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    [Surjective x] [IsProper r] [LocallyOfFinitePresentation r]
    (hpb : IsPullback a x r (c.π.app i)) :
    ∃ (j : J) (h : j ⟶ i), Surjective (pullback.snd r (D.map h)) ∧
      ∃ a' : X ⟶ pullback r (D.map h),
        IsPullback a' x (pullback.snd r (D.map h)) (c.π.app j) ∧
        a' ≫ pullback.fst r (D.map h) = a := by
  haveI : Surjective (pullback.snd r (c.π.app i)) := stage_surjective_pullback_snd hpb
  obtain ⟨j, h, hsurj⟩ := exists_surjective_proper_pullback_of_isLimit D hc r
  exact ⟨j, h, hsurj, stage_model_map_of_isPullback D c h a x r hpb⟩

/-- 平坦な模型の全射性が降りる段で、同じ模型の実際の射と Cartesian 性を保持する。 -/
theorem exists_surjective_flat_stage_model
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)]
    {i : J} {X T : Scheme.{u}} (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    [Surjective x] [Flat r] [LocallyOfFinitePresentation r] [QuasiCompact r]
    (hpb : IsPullback a x r (c.π.app i)) :
    ∃ (j : J) (h : j ⟶ i), Surjective (pullback.snd r (D.map h)) ∧
      ∃ a' : X ⟶ pullback r (D.map h),
        IsPullback a' x (pullback.snd r (D.map h)) (c.π.app j) ∧
        a' ≫ pullback.fst r (D.map h) = a := by
  haveI : Surjective (pullback.snd r (c.π.app i)) := stage_surjective_pullback_snd hpb
  obtain ⟨j, h, hsurj⟩ := exists_surjective_flat_pullback_of_isLimit D c hc r
  exact ⟨j, h, hsurj, stage_model_map_of_isPullback D c h a x r hpb⟩

end SerrePositivity.AlgebraicGeometry
