module

public import SerrePositivity.AlgebraicGeometry.BaseChangeCharts
public import SerrePositivity.AlgebraicGeometry.ChartGluing
public import SerrePositivity.AlgebraicGeometry.FlatBlowupChartBaseChange

/-!
概要：アフィン基底のブローアップは平坦底変換と可換。
方針：標準チャート上の環のテンソル積を Spec の引き戻しにし、チャート被覆で貼り合わせる。
規約：比較には既存のブローアップの係数写像を用いる。
使われ方：共通中心のブローアップを étale 局所中心のブローアップと比較する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

private theorem isPullback_affineBlowupChart_of_flat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (I : Ideal R) (a : I) :
    let f := algebraMap R S
    let J := I.map f
    let a' := centerImageElement I J f le_rfl a
    IsPullback (Spec.map (CommRingCat.ofHom (chartBaseChangeMap I J f le_rfl a)))
      (Spec.map (CommRingCat.ofHom (chartBaseMap J a')))
      (Spec.map (CommRingCat.ofHom (chartBaseMap I a))) (Spec.map (CommRingCat.ofHom f)) := by
  let f := algebraMap R S
  let J := I.map f
  let a' := centerImageElement I J f le_rfl a
  let C := BlowupChartRing I a
  let : Algebra R C := (chartBaseMap I a).toAlgebra
  obtain ⟨e, h₁, h₂⟩ := exists_chartTensorEquiv_of_flat (S := S) I a
  apply isPullback_SpecMap_of_isPushout
  refine (CommRingCat.isPushout_tensorProduct R C S).of_iso (.refl _) (.refl _) (.refl _)
    e.toCommRingCatIso (by simp) (by simp) ?_ ?_
  · exact CommRingCat.hom_ext (RingHom.ext h₁)
  · exact CommRingCat.hom_ext (RingHom.ext h₂)

/--
概要：平坦な係数環へのアフィンブローアップの比較射は、基底変換の引き戻しを与える。
方針：チャート環の底変換同型と、比較射による標準開の逆像公式を組み合わせる。
規約：像中心はイデアルの拡大で表す。
使われ方：Stacks 0814 で、基底の共通中心を étale チャート上の積中心に移す。
-/
theorem isPullback_affineBlowupBaseMap_of_flat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] (I : Ideal R) :
    IsPullback (affineBlowupBaseMap I (algebraMap R S))
      (affineBlowupπ (I.map (algebraMap R S))) (affineBlowupπ I)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let f := algebraMap R S
  let J := I.map f
  let p := affineBlowupBaseMap I f
  let 𝒰 := (affineBlowupChartCover I).openCover
  refine Scheme.isPullback_of_openCover _ _ _ _ 𝒰 fun a => ?_
  let a' := centerImageElement I J f le_rfl a
  let i := affineBlowupChartι I a
  let i' := affineBlowupChartι J a'
  let j := Spec.map (CommRingCat.ofHom (chartBaseChangeMap I J f le_rfl a))
  let : IsOpenImmersion i := affineBlowupChartι_isOpenImmersion I a
  let : IsOpenImmersion i' := affineBlowupChartι_isOpenImmersion J a'
  have hOpen : IsPullback j i' i p := by
    apply IsOpenImmersion.isPullback
    · exact affineBlowupBaseMap_chart I f a
    · rw [show i.opensRange = affineBlowupChart I a from Proj.opensRange_awayι ..,
        show i'.opensRange = affineBlowupChart J a' from
          Proj.opensRange_awayι ..]
      exact affineBlowupBaseMap_preimage_chart I f a
  let e := hOpen.flip.isoPullback
  have hCart : IsPullback j (i' ≫ affineBlowupπ J)
      (i ≫ affineBlowupπ I) (Spec.map (CommRingCat.ofHom f)) := by
    rw [show i ≫ affineBlowupπ I = Spec.map (CommRingCat.ofHom (chartBaseMap I a)) from
      affineBlowupChartIso_inv_ι_π I a,
      show i' ≫ affineBlowupπ J = Spec.map (CommRingCat.ofHom (chartBaseMap J a')) from
      affineBlowupChartIso_inv_ι_π J a']
    exact isPullback_affineBlowupChart_of_flat (S := S) I a
  refine hCart.of_iso e (.refl _) (.refl _) (.refl _) ?_ ?_ ?_ (by simp)
  · change j ≫ 𝟙 _ = e.hom ≫ pullback.snd p i
    rw [Category.comp_id]
    exact hOpen.flip.isoPullback_hom_snd.symm
  · change (i' ≫ affineBlowupπ J) ≫ 𝟙 _ = e.hom ≫ pullback.fst p i ≫ affineBlowupπ J
    rw [Category.comp_id, ← Category.assoc, show e.hom ≫ pullback.fst p i = i' from
      hOpen.flip.isoPullback_hom_fst]
  · change (i ≫ affineBlowupπ I) ≫ 𝟙 _ = 𝟙 _ ≫ i ≫ affineBlowupπ I
    simp

end SerrePositivity.AlgebraicGeometry
