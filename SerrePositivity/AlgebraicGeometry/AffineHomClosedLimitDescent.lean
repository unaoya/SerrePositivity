module

public import SerrePositivity.AlgebraicGeometry.AffineRestrictionClosedLimit
public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
概要：一般の標的の有限 affine 被覆上の閉埋め込み性を同じ段に降ろして貼り合わせる。
方針：二段の pullback の実際の同型と閉埋め込み性の標的での局所性を使う。
規約：ここでは元の射は affine。一般の場合の affine 性の降下は別に接続する。
使われ方：Stacks 01ZP の一般の閉埋め込み性の降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 合成の底変換の閉埋め込み性を、二段の実際の pullback の第二射影へ移す。 -/
theorem isClosedImmersion_baseChange_restriction
    {X S T V : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (h : V ⟶ T)
    (b : V ⟶ S) (hb : h ≫ g = b)
    [IsClosedImmersion (pullback.fst b f)] :
    IsClosedImmersion (pullback.snd (pullback.snd f g) h) := by
  haveI : IsClosedImmersion (pullback.snd f b) := by
    have H : IsClosedImmersion ((pullbackSymmetry f b).hom ≫ pullback.fst b f) := inferInstance
    simpa using H
  let sq := isPullback_pullbackCompositeMap f g h b hb
  have H : IsClosedImmersion (sq.isoPullback.inv ≫ pullback.snd f b) := inferInstance
  simpa only [IsPullback.isoPullback_inv_snd] using H

/-- affine・局所有限型の射の極限での閉埋め込み性を一般の標的の有限段へ降ろす。 -/
theorem exists_closedImmersion_pullback_of_isLimit_of_isAffineHom
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {j k} (a : j ⟶ k), IsAffineHom (D.map a)]
    {i : J} [CompactSpace (D.obj i)] {X : Scheme.{u}} (f : X ⟶ D.obj i)
    [IsAffineHom f] [LocallyOfFiniteType f]
    [IsClosedImmersion (pullback.snd f (c.π.app i))] :
    ∃ (j : J) (a : j ⟶ i), IsClosedImmersion (pullback.snd f (D.map a)) := by
  let 𝒰 := (D.obj i).affineCover.finiteSubcover
  haveI (a : 𝒰.I₀) : IsAffine (𝒰.X a) := by
    dsimp only [𝒰]
    rw [Scheme.OpenCover.finiteSubcover_X]
    infer_instance
  obtain ⟨j, hj⟩ := exists_finite_closedImmersion_restricted_stage D c hc f 𝒰.X 𝒰.f
  let 𝒱 : (D.obj j.left).OpenCover := Scheme.Cover.mkOfCovers 𝒰.I₀
    (fun a ↦ pullback (D.map j.hom) (𝒰.f a))
    (fun a ↦ pullback.fst (D.map j.hom) (𝒰.f a)) (by
      intro x
      obtain ⟨a, y, hy⟩ := 𝒰.exists_eq (D.map j.hom x)
      obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
        (IsPullback.of_hasPullback (D.map j.hom) (𝒰.f a)) x y hy.symm
      exact ⟨a, z, hz⟩)
  refine ⟨j.left, j.hom, ?_⟩
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) 𝒱
  intro a
  change IsClosedImmersion (pullback.snd (pullback.snd f (D.map j.hom))
    (pullback.fst (D.map j.hom) (𝒰.f a)))
  letI : IsClosedImmersion
      (pullback.fst (pullback.snd (D.map j.hom) (𝒰.f a) ≫ 𝒰.f a) f) := hj a
  exact isClosedImmersion_baseChange_restriction f (D.map j.hom)
    (pullback.fst (D.map j.hom) (𝒰.f a))
    (pullback.snd (D.map j.hom) (𝒰.f a) ≫ 𝒰.f a) pullback.condition

end SerrePositivity.AlgebraicGeometry
