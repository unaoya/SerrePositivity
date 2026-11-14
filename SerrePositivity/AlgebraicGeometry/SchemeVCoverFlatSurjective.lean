module

public import SerrePositivity.AlgebraicGeometry.SchemeVCover
public import SerrePositivity.AlgebraicGeometry.AffineVCoverFaithfullyFlat
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
概要：平坦全射の任意の付値環に関する持ち上げを供給する。
方針：付値環の閉点上の affine チャートを取り、一般化の持ち上げで全射にする。
規約：既存の忠実平坦な環準同型の付値持ち上げを使い、有限表示を要求しない。
使われ方：B03 の fppf 因子と、その有限係数模型の v 判定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 平坦全射は、任意の階数の付値環に関するスキームの v 判定を満たす。 -/
theorem isSchemeVCover_of_flat_surjective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [Surjective f] : IsSchemeVCover f := by
  intro V _ _ k
  let P := pullback f k
  let π := pullback.snd f k
  obtain ⟨x, hx⟩ := π.surjective (IsLocalRing.closedPoint V)
  let 𝒰 := P.affineCover
  obtain ⟨i, z, hz⟩ := 𝒰.exists_eq x
  let g := 𝒰.f i ≫ π
  haveI : Flat g := by dsimp [g, π]; infer_instance
  have hgz : g z = IsLocalRing.closedPoint V := by
    change π (𝒰.f i z) = _
    rw [hz, hx]
  haveI : Surjective g := ⟨by
    intro y
    have hy : y ⤳ g z := by
      rw [hgz]
      exact IsLocalRing.specializes_closedPoint y
    obtain ⟨z', _, hz'⟩ := Flat.generalizingMap g hy
    exact ⟨z', hz'⟩⟩
  let g' := (𝒰.X i).isoSpec.inv ≫ g
  obtain ⟨h, hh⟩ := Spec.map_surjective g'
  haveI : Flat (Spec.map h) := by rw [hh]; dsimp [g']; infer_instance
  haveI : Surjective (Spec.map h) := by rw [hh]; dsimp [g']; infer_instance
  have hff := (flat_and_surjective_SpecMap_iff h).mp ⟨inferInstance, inferInstance⟩
  have hv : IsSchemeVCover (Spec.map h) :=
    (isSchemeVCover_specMap_iff h.hom).mpr (isAffineVCover_of_faithfullyFlat h.hom hff)
  obtain ⟨W, hW, hval, e, l, he, hl⟩ := hv V (𝟙 _)
  have hl' : l ≫ g' = Spec.map (CommRingCat.ofHom e) := by
    rw [← hh]
    exact hl.trans (Category.comp_id _)
  refine ⟨W, hW, hval, e,
    l ≫ (𝒰.X i).isoSpec.inv ≫ 𝒰.f i ≫ pullback.fst f k, he, ?_⟩
  calc
    (l ≫ (𝒰.X i).isoSpec.inv ≫ 𝒰.f i ≫ pullback.fst f k) ≫ f = l ≫ g' ≫ k := by
      dsimp [g', g, π]
      simp only [Category.assoc, pullback.condition]
    _ = Spec.map (CommRingCat.ofHom e) ≫ k := by rw [← Category.assoc, hl']

end SerrePositivity.AlgebraicGeometry
