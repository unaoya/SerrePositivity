module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.DisjointCenterGluing
public import SerrePositivity.AlgebraicGeometry.AffineBlowupNoetherian

/-!
概要：KST §5、Stacks Lemma 31.35.5・0811 の互いに交わらない標準 blowup チャート上の中心の大域化。
方針：環イデアルを Spec のイデアル層へ移し、開閉被覆の正確な貼り合わせを適用する。
規約：中心補開集合とチャートへの制限等式をともに保持する。
使われ方：階数を分離した第一段の blowup 上で、第二段の局所中心を一つにまとめる。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/--
概要：有限個の互いに交わらない標準チャート上の中心を、第一段の blowup 上の一つの実際の中心へ貼り合わせる。
方針：Spec のイデアル対応と標準チャートの構造射を使い、制限等式と補開集合を照合する。
規約：KST §5、Stacks Lemma 31.35.5・0811、基礎環は Noether。
使われ方：二段自由化中心の第二段を大域イデアル層として実現する。
-/
theorem exists_disjointBlowupChart_center
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) {ι : Type v} [Finite ι] (a : ι → I)
    (hcover : (⨆ i, affineBlowupChart I (a i)) = ⊤)
    (hd : Pairwise (fun i k => Disjoint (affineBlowupChart I (a i)) (affineBlowupChart I (a k))))
    (f : R) (J : ∀ i, Ideal (BlowupChartRing I (a i)))
    (hJ : ∀ i, affineCenterComplement (J i) = PrimeSpectrum.basicOpen (chartBaseMap I (a i) f)) :
    ∃ L : (affineBlowup I).IdealSheafData,
      (∀ V : (affineBlowup I).affineOpens, (L.ideal V).FG) ∧
      centerComplement L = affineBlowupπ I ⁻¹ᵁ PrimeSpectrum.basicOpen f ∧
      ∀ i, specIdealEquiv (.of (BlowupChartRing I (a i)))
        (L.comap (affineBlowupChartι I (a i))) = J i := by
  let X (i : ι) := Spec (CommRingCat.of (BlowupChartRing I (a i)))
  let j (i : ι) : X i ⟶ affineBlowup I := affineBlowupChartι I (a i)
  let : ∀ i, IsOpenImmersion (j i) := fun i => inferInstance
  let : ∀ i, QuasiCompact (j i) := fun i => by
    let : IsNoetherianRing (BlowupChartRing I (a i)) := blowupChartRing_isNoetherianRing I (a i)
    infer_instance
  let K (i : ι) : (X i).IdealSheafData :=
    (specIdealEquiv (.of (BlowupChartRing I (a i)))).symm (J i)
  let U := affineBlowupπ I ⁻¹ᵁ PrimeSpectrum.basicOpen f
  have hrange (i : ι) : (j i).opensRange = affineBlowupChart I (a i) :=
    Proj.opensRange_awayι ..
  have hcover' : (⨆ i, (j i).opensRange) = ⊤ := by simpa only [hrange] using hcover
  have hd' : Pairwise (fun i k => Disjoint (j i).opensRange (j k).opensRange) := by
    intro i k hik
    simpa only [hrange] using hd hik
  have hKU (i : ι) : centerComplement (K i) = j i ⁻¹ᵁ U := by
    have he : specIdealEquiv (.of (BlowupChartRing I (a i))) (K i) = J i :=
      (specIdealEquiv _).apply_symm_apply _
    rw [centerComplement_specIdealEquiv, he, hJ]
    ext x
    change x ∈ PrimeSpectrum.basicOpen (chartBaseMap I (a i) f) ↔
      (affineBlowupChartι I (a i) ≫ affineBlowupπ I) x ∈ PrimeSpectrum.basicOpen f
    have hbase : affineBlowupChartι I (a i) ≫ affineBlowupπ I =
        Spec.map (CommRingCat.ofHom (chartBaseMap I (a i))) :=
      affineBlowupChartIso_inv_ι_π I (a i)
    with_reducible_and_instances rw [hbase]
    rfl
  obtain ⟨L, hfg, hrest, hU⟩ := exists_center_of_disjoint_open_cover j hcover' hd' U K hKU
  refine ⟨L, hfg, hU, ?_⟩
  intro i
  change specIdealEquiv (.of (BlowupChartRing I (a i))) (L.comap (j i)) = J i
  rw [hrest]
  exact (specIdealEquiv _).apply_symm_apply _

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
