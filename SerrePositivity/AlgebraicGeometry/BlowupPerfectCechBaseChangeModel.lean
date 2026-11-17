module

public import SerrePositivity.AlgebraicGeometry.BlowupPerfectCechBaseChangeData
public import SerrePositivity.AlgebraicGeometry.IdealComplementPullback
public import SerrePositivity.AlgebraicGeometry.OpenImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
概要：固定したブローアップの任意のNoetherアフィン試験基底の表示を作る。
方針：元のアフィン基底の次数一表示を環の射で底変換し、中心は同じ核で比較する。
規約：底変換後のブローアップとの一致は用いず、同じ元の射のpullbackを表示する。
使われ方：閉中心を使う普遍Čech降下の射影的な段（承認済み計画I02）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.isDefEq.respectTransparency false

/-- 元のブローアップの同じpullbackに、中心・射影・中心外の表示を供給する。 -/
def blowupPerfectCechBaseChangeData
    {Y : Scheme.{u}} [IsAffine Y] [_root_.AlgebraicGeometry.IsNoetherian Y]
    (J : Y.IdealSheafData) {A : Type u} [CommRing A] [IsNoetherianRing A]
    (t : Spec (CommRingCat.of A) ⟶ Y) : BlowupPerfectCechBaseChangeData J t := by
  classical
  let I := specIdealEquiv (CommRingCat.of A) (J.comap t)
  let c := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ 1)))
  haveI : IsClosedImmersion c := by
    dsimp only [c]
    exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hker : c.ker = (J.comap t).subschemeι.ker := by
    apply (specIdealEquiv (CommRingCat.of A)).injective
    rw [Scheme.IdealSheafData.ker_subschemeι]
    change specIdealEquiv (CommRingCat.of A) c.ker = I
    dsimp only [c]
    rw [← Scheme.IdealSheafData.map_bot, specIdealEquiv_map, OrderIso.map_bot]
    change RingHom.ker (Ideal.Quotient.mk (I ^ 1)) = I
    rw [Ideal.mk_ker, pow_one]
  let e := IsClosedImmersion.lift c (J.comap t).subschemeι hker.le
  haveI : IsIso e := IsClosedImmersion.isIso_lift c (J.comap t).subschemeι hker
  let B := Γ(Y, ⊤)
  haveI : IsNoetherianRing B :=
    IsLocallyNoetherian.component_noetherian (X := Y) ⟨⊤, isAffineOpen_top Y⟩
  let j := Y.isoSpec.inv
  let m := Classical.choice (nonempty_blowupAffinePullbackProjectiveModel j J
    (Ideal.fg_of_isNoetherianRing _))
  let q : B →+* A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp t.appTop.hom
  have hq : Spec.map (CommRingCat.ofHom q) ≫ j = t := by
    change Spec.map (t.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom) ≫ Y.isoSpec.inv = t
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_hom, Category.assoc,
      Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
  let m₁ := m.baseChange q
  let E := pullbackLeftPullbackSndIso (blowupπ J) j (Spec.map (CommRingCat.ofHom q))
  have hE : E.inv ≫ pullback.snd (pullback.snd (blowupπ J) j)
      (Spec.map (CommRingCat.ofHom q)) =
        pullback.snd (blowupπ J) (Spec.map (CommRingCat.ofHom q) ≫ j) :=
    pullbackLeftPullbackSndIso_inv_snd_snd _ _ _
  have hm : Nonempty (DegreeOneProjectiveModel (R := A) (pullback.snd (blowupπ J) t)) := by
    rw [← hq]
    exact ⟨hE ▸ m₁.ofIso E.symm⟩
  have hout : IsIso (pullback.snd (blowupπ J) t ∣_ affineCenterComplement I) := by
    haveI := blowupπ_restrict_complement_isIso J
    have h := pullback_snd_restrict_isIso (blowupπ J) t (centerComplement J)
    rw [affine_preimage_centerComplement] at h
    exact h
  exact
    { ideal := I
      centerIso := asIso e
      center_over := IsClosedImmersion.lift_fac _ _ _
      model := Classical.choice hm
      outside := hout }

end SerrePositivity.AlgebraicGeometry
