module

public import SerrePositivity.AlgebraicGeometry.BaseChangePairAffine
public import SerrePositivity.AlgebraicGeometry.FiniteAffineCompositeStages
public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
概要：qcqs な逆極限での射の affine 性を、一般の標的のある有限段へ降ろす。
方針：標的の有限 affine 被覆の制限の源を同じ段で affine にし、局所性を使う。
規約：Stacks 01ZN。係数射の忠実平坦性・標的の Noether 性は要求しない。
使われ方：C04 の一般の閉埋め込み性の有限段への降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- qcqs な射の極限での affine 性は、一般の標的のある後の段へ降りる。 -/
theorem exists_affineHom_pullback_of_isLimit
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {i : J} {X : Scheme.{u}} (f : X ⟶ D.obj i)
    [QuasiCompact f] [QuasiSeparated f] [IsAffineHom (pullback.snd f (c.π.app i))] :
    ∃ (j : J) (a : j ⟶ i), IsAffineHom (pullback.snd f (D.map a)) := by
  let 𝒰 := (D.obj i).affineCover.finiteSubcover
  haveI (a : 𝒰.I₀) : IsAffine (𝒰.X a) := by
    dsimp only [𝒰]
    rw [Scheme.OpenCover.finiteSubcover_X]
    infer_instance
  let Y (a : 𝒰.I₀) := pullback f (𝒰.f a)
  let p (a : 𝒰.I₀) : Y a ⟶ D.obj i := pullback.fst f (𝒰.f a) ≫ f
  haveI (a : 𝒰.I₀) : QuasiCompact (𝒰.f a) := inferInstance
  haveI (a : 𝒰.I₀) : QuasiCompact (p a) := by dsimp [p]; infer_instance
  haveI (a : 𝒰.I₀) : QuasiSeparated (p a) := by dsimp [p]; infer_instance
  letI : IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc i
  haveI (a : 𝒰.I₀) : IsAffine (pullback (p a) (c.π.app i)) :=
    isAffine_restrictedSource_of_baseChangeAffine f (𝒰.f a) (c.π.app i)
  obtain ⟨j, hj⟩ := exists_finite_affine_compositeStage_of_isLimit D c hc i (𝟙 _)
    (c.π.app i) (by simp) Y p
  let 𝒱 : (D.obj j.left).OpenCover := Scheme.Cover.mkOfCovers 𝒰.I₀
    (fun a ↦ pullback (𝒰.f a) (D.map j.hom))
    (fun a ↦ pullback.snd (𝒰.f a) (D.map j.hom)) (by
      intro x
      obtain ⟨a, y, hy⟩ := 𝒰.exists_eq (D.map j.hom x)
      obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback
        (IsPullback.of_hasPullback (𝒰.f a) (D.map j.hom)) y x hy
      exact ⟨a, z, hz⟩)
  refine ⟨j.left, j.hom, ?_⟩
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsAffineHom) 𝒱
  intro a
  change IsAffineHom (pullback.snd (pullback.snd f (D.map j.hom))
    (pullback.snd (𝒰.f a) (D.map j.hom)))
  letI : IsAffine (pullback (𝒰.f a) (D.map j.hom)) := inferInstance
  letI : IsAffine (pullback (D.map j.hom) (p a)) := by
    simpa only [Category.comp_id] using hj a
  letI : IsAffine (pullback (p a) (D.map j.hom)) :=
    isAffine_of_isAffineHom (pullbackSymmetry (p a) (D.map j.hom)).hom
  letI : IsAffine (pullback (pullback.snd f (D.map j.hom))
      (pullback.snd (𝒰.f a) (D.map j.hom))) :=
    isAffine_of_isAffineHom (baseChangePairIso f (𝒰.f a) (D.map j.hom)).hom
  infer_instance

end SerrePositivity.AlgebraicGeometry
