module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ProductBlowup

/-!
概要：KST §5、Stacks 080Y の降下中心を積中心の blowup 上で可逆化する局所環論。
方針：降下等式 J = aᴰ K を積チャートへ移し、正則単項イデアルの因子を消去する。
規約：実際の標準チャートの環準同型を使う。
使われ方：二段の blowup を基底上の積中心で支配する射の構成。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
variable {R : Type u} [CommRing R] (I J : Ideal R) (a : I) (b : J)

/--
概要：積中心の ab チャートへの第一のチャート環の実際の持ち上げ。
方針：積チャートで I が正則な a により生成されることを使う。
規約：KST §5、Stacks 080Y、環の向きは第一の blowup から積中心チャート。
使われ方：降下した中心のイデアルの像の計算。
-/
def productLeftChartRingMap : BlowupChartRing I a →+*
    BlowupChartRing (I * J) (mulCenterElement I J a b) :=
  chartRegularLift I (chartBaseMap (I * J) (mulCenterElement I J a b)) a
    (productChart_left_regular I J a b) (productChart_left_image I J a b)

/--
概要：積中心の第一のチャート持ち上げは基礎環の係数を保存する。
方針：正則持ち上げの係数保存を使う。
規約：KST §5、Stacks 080Y、同じ基礎環 R 上の等式。
使われ方：降下イデアルの像を積中心のチャートで評価する。
-/
@[simp] theorem productLeftChartRingMap_base (r : R) :
    productLeftChartRingMap I J a b (chartBaseMap I a r) =
      chartBaseMap (I * J) (mulCenterElement I J a b) r :=
  chartRegularLift_base ..

/--
概要：aᴰ 倍が基底中心 J から降りるチャートイデアルは、積中心の ab チャートで正則単項になる。
方針：基底中心 J の像は正則な b で生成されるので、aᴰ 倍を消去する。
規約：KST §5、Stacks 080Y、有限生成性や Noether 性はこの局所補題には不要。
使われ方：二段目の blowup への局所的な普遍写像。
-/
theorem productLeftChartRingMap_regular_center
    (K : Ideal (BlowupChartRing I a)) (D : ℕ)
    (hJ : J.map (chartBaseMap I a) = Ideal.span {chartBaseMap I a a.1 ^ D} * K) :
    ∃ c : BlowupChartRing (I * J) (mulCenterElement I J a b),
      c ∈ nonZeroDivisors _ ∧ K.map (productLeftChartRingMap I J a b) = Ideal.span {c} := by
  let ψ := productLeftChartRingMap I J a b
  let φ := chartBaseMap (I * J) (mulCenterElement I J a b)
  have hcomp : ψ.comp (chartBaseMap I a) = φ := by
    apply RingHom.ext
    intro r
    exact productLeftChartRingMap_base I J a b r
  have hmap : J.map φ = Ideal.span {φ a.1 ^ D} * K.map ψ := by
    calc
      _ = (J.map (chartBaseMap I a)).map ψ := by rw [Ideal.map_map, hcomp]
      _ = _ := by
        rw [hJ, Ideal.map_mul, Ideal.map_span, Set.image_singleton, map_pow]
        rw [show ψ (chartBaseMap I a a.1) = φ a.1 from productLeftChartRingMap_base I J a b a.1]
  obtain ⟨c, hc, hK, _⟩ := ideal_regular_principal_of_regular_multiple (K.map ψ)
    (φ a.1 ^ D) (φ b.1) (productChart_right_regular I J a b)
    (hmap.symm.trans (productChart_right_image I J a b))
  exact ⟨c, hc, hK⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
