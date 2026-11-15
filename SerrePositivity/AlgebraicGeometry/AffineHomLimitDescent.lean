module

public import SerrePositivity.AlgebraicGeometry.FiniteAffineCompositeStages

/-!
概要：affine な標的の段について、射の affine 性を有限段へ降ろす。
方針：極限の基底と源を affine とし、実際の源の affine 性をある段へ移す。
規約：Stacks 01ZN の affine な標的の場合。一般の標的は有限被覆で別に扱う。
使われ方：C04 の閉埋め込み性の降下の最初の帰着。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- affine な標的の段への射の極限での affine 性は、ある後の段へ降りる。 -/
theorem exists_affineHom_pullback_of_isLimit_of_affine
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {i : J} [IsAffine (D.obj i)] {X : Scheme.{u}} (f : X ⟶ D.obj i)
    [QuasiCompact f] [QuasiSeparated f] [IsAffineHom (pullback.snd f (c.π.app i))] :
    ∃ (j : J) (a : j ⟶ i), IsAffineHom (pullback.snd f (D.map a)) := by
  letI : IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc i
  letI : IsAffine c.pt := isAffine_of_isAffineHom (c.π.app i)
  letI : IsAffine (((Functor.const J).obj c.pt).obj i) := inferInstanceAs (IsAffine c.pt)
  letI : IsAffine (pullback f (c.π.app i)) := isAffine_of_isAffineHom (pullback.snd f (c.π.app i))
  obtain ⟨j, hj⟩ := exists_affine_compositeStage_of_isLimit D c hc i (𝟙 _) (c.π.app i) (by simp) f
  letI : IsAffine (pullback (D.map j.hom) f) := by simpa only [Category.comp_id] using hj
  letI : IsAffine (D.obj j.left) := isAffine_of_isAffineHom (D.map j.hom)
  letI : IsAffine (pullback f (D.map j.hom)) :=
    isAffine_of_isAffineHom (pullbackSymmetry f (D.map j.hom)).hom
  exact ⟨j.left, j.hom, inferInstance⟩

end SerrePositivity.AlgebraicGeometry
