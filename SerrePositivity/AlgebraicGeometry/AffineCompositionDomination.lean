module

public import SerrePositivity.AlgebraicGeometry.ProductLiftCenter
public import SerrePositivity.AlgebraicGeometry.OpenChartUniversal
public import SerrePositivity.AlgebraicGeometry.AffineCenterDescentSheaf

/-!
概要：KST §5、Stacks 080Y の Noether アフィン基底上の二段の blowup の共通支配。
方針：二段目の中心を例外イデアルの冪で降ろし、積中心のチャートで可逆化して普遍写像を貼り合わせる。
規約：実際の射と構造射の交換式を構成する。admissible 性の移送は別途扱う。
使われ方：有限回の admissible blowup を一つの基底中心で支配する帰納法。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {R : Type u} [CommRing R] (I J : Ideal R)
  (K : (affineBlowup I).IdealSheafData)

set_option backward.isDefEq.respectTransparency false in
/--
概要：二段目の中心の捻りが基底の J へ降りるなら、積中心の blowup から二段目への支配射が存在する。
方針：積生成元チャートで中心を正則単項にし、任意の開チャートの普遍写像を貼り合わせる。
規約：KST §5、Stacks 080Y、降下条件は各環イデアルの等式で明示する。
使われ方：Noether アフィン基底で実際の中心降下を支配射へ移す。
-/
theorem exists_affine_composition_lift_of_descent (D : ℕ)
    (hJ : ∀ a : I, J.map (chartBaseMap I a) =
      Ideal.span {chartBaseMap I a a.1 ^ D} * blowupChartIdeal I K a) :
    ∃ g : affineBlowup (I * J) ⟶ blowup K,
      g ≫ blowupπ K = affineBlowupProductLeftMap I J := by
  classical
  let 𝒰 := affineBlowupProductChartCover I J
  let A (p : I × J) := CommRingCat.of (BlowupChartRing I p.1)
  let j (p : I × J) : Spec (A p) ⟶ affineBlowup I := affineBlowupChartι I p.1
  have hj (p : I × J) : IsOpenImmersion (j p) := inferInstance
  let φ (p : I × J) : A p ⟶ 𝒰.X p := CommRingCat.ofHom (productLeftChartRingMap I J p.1 p.2)
  choose c hreg hc using fun p : I × J => productLeftChartRingMap_regular_center I J p.1 p.2
    (blowupChartIdeal I K p.1) D (hJ p.1)
  have hbase (p : I × J) : Spec.map (φ p) ≫ j p =
      𝒰.f p ≫ affineBlowupProductLeftMap I J := by
    change productBlowupLeftChartMap I J p.1 p.2 =
      (affineBlowupProductChartCover I J).openCover.f p ≫ affineBlowupProductLeftMap I J
    rw [affineBlowupProductLeftMap, Scheme.Cover.ι_glueMorphisms]
  exact ⟨openChartUniversalLift K (affineBlowupProductLeftMap I J) 𝒰 A j hj φ c hreg hc hbase,
    openChartUniversalLift_base K (affineBlowupProductLeftMap I J) 𝒰 A j hj φ c hreg hc hbase⟩

/--
概要：Noether アフィン基底の二段の通常 blowup は一つの通常 blowup で基底上共通支配される。
方針：中心の降下で得た J と元の中心 I の積を新しい中心とする。
規約：KST §5、Stacks 080Y、二段目の中心は任意の実際のイデアル層。
使われ方：admissible blowup の合成の支配のアフィン部分。
-/
theorem exists_affine_blowup_composition_domination [IsNoetherianRing R] :
    ∃ L : Ideal R, L.FG ∧ ∃ g : affineBlowup L ⟶ blowup K,
      g ≫ blowupπ K ≫ affineBlowupπ I = affineBlowupπ L := by
  obtain ⟨N, hN⟩ := exists_affine_center_descent I K
  obtain ⟨J, _, _, hJ⟩ := hN N le_rfl
  have hchart (a : I) : J.map (chartBaseMap I a) =
      Ideal.span {chartBaseMap I a a.1 ^ N} * blowupChartIdeal I K a := by
    rw [← blowupChartIdeal_base_comap I J a, hJ, blowupChartIdeal_mul, blowupChartIdeal_pow,
      affineExceptionalIdealSheaf_chart, Ideal.span_singleton_pow]
  obtain ⟨g, hg⟩ := exists_affine_composition_lift_of_descent I J K N hchart
  exact ⟨I * J, Ideal.fg_of_isNoetherianRing _, g,
    by rw [← Category.assoc, hg, affineBlowupProductLeftMap_base]⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
