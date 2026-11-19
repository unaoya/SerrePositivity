module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ProductCenter
public import SerrePositivity.AlgebraicGeometry.ChartGluing

/-!
概要：KST §5、Stacks 080Y の共通細分に使う積中心のチャート被覆。
方針：IJ が積 ab で生成されることを Rees の次数一元と素イデアルに移す。
規約：有限生成性や Noether 性を使わない。
使われ方：Bl_{IJ} から両因子の blowup への射を貼り合わせる。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open Polynomial _root_.AlgebraicGeometry
variable {R : Type u} [CommRing R] (I J : Ideal R)

/--
概要：全ての積生成元の Rees 次数一元を含むイデアルは次数一成分全体を含む。
方針：次数一の単項式の逆像部分加群でイデアルの積の生成性を使う。
規約：KST §5、Stacks 080Y、素性自体はこの補題には不要。
使われ方：積生成元チャートの被覆性の環論的入力。
-/
theorem contains_degreeOne_of_contains_products (P : Ideal (reesAlgebra (I * J)))
    (hP : ∀ (a : I) (b : J), reesDegreeOne (I * J) (mulCenterElement I J a b) ∈ P) :
    ∀ c : ↥(I * J), reesDegreeOne (I * J) c ∈ P := by
  let T : Submodule R R :=
    ((P.restrictScalars R).map (reesAlgebra (I * J)).val.toLinearMap).comap (monomial 1)
  have hspan : I * J ≤ T := by
    apply Ideal.mul_le.mpr
    intro a ha b hb
    change monomial 1 (a * b) ∈
      (P.restrictScalars R).map (reesAlgebra (I * J)).val.toLinearMap
    exact ⟨reesDegreeOne (I * J) (mulCenterElement I J ⟨a, ha⟩ ⟨b, hb⟩),
      hP ⟨a, ha⟩ ⟨b, hb⟩, rfl⟩
  intro c
  obtain ⟨p, hp, heq⟩ := hspan c.2
  have heq' : p = reesDegreeOne (I * J) c := Subtype.ext heq
  rwa [← heq']

/--
概要：積中心 IJ の blowup は ab に対応する標準チャートで覆われる。
方針：被覆に入らない斉次素イデアルが全ての次数一元を含む矛盾を得る。
規約：KST §5、Stacks 080Y、a ∈ I と b ∈ J で添字付けする。
使われ方：積中心による共通細分の比較射の貼り合わせ。
-/
theorem iSup_affineBlowup_productCharts :
    ⨆ p : I × J, affineBlowupChart (I * J) (mulCenterElement I J p.1 p.2) = ⊤ := by
  classical
  apply top_unique
  intro x _
  by_contra hnot
  have hP (a : I) (b : J) : reesDegreeOne (I * J) (mulCenterElement I J a b) ∈
      x.asHomogeneousIdeal.toIdeal := by
    by_contra ha
    exact hnot (TopologicalSpace.Opens.mem_iSup.mpr ⟨(a, b), ha⟩)
  have hall := contains_degreeOne_of_contains_products I J x.asHomogeneousIdeal.toIdeal hP
  have htop : x ∈ (⊤ : (affineBlowup (I * J)).Opens) := trivial
  rw [← iSup_affineBlowupChart (I * J)] at htop
  obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.mp htop
  exact hc (hall c)

/--
概要：積生成元の標準チャートによる実際のアフィン開被覆。
方針：積チャートの被覆性から点ごとの添字を選ぶ。
規約：KST §5、Stacks 080Y、中心は I J。
使われ方：両因子への共通細分の比較射の定義。
-/
def affineBlowupProductChartCover : (affineBlowup (I * J)).AffineOpenCover where
  I₀ := I × J
  X p := CommRingCat.of (BlowupChartRing (I * J) (mulCenterElement I J p.1 p.2))
  f p := affineBlowupChartι (I * J) (mulCenterElement I J p.1 p.2)
  idx x := (TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineBlowup_productCharts I J).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (affineBlowupChartι (I * J) _).opensRange
    rw [show (affineBlowupChartι (I * J) _).opensRange = affineBlowupChart (I * J) _ from
      Proj.opensRange_awayι ..]
    exact (TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineBlowup_productCharts I J).ge (Set.mem_univ x))).choose_spec

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
