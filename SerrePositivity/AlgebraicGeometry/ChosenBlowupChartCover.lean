module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.GeneratorChartCover

/-!
概要：KST §5、Stacks 0811 の指定した標準チャートによる blowup のアフィン開被覆。
方針：チャート開集合の上限が全体であることから点ごとの添字を選ぶ。
規約：被覆性を直接入力し、中心の生成族であることは要求しない。
使われ方：一般階数を分離した実際の開閉チャート族を第二段の被覆に使う。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry

/--
概要：全体を覆うように選んだ標準 blowup チャート族を実際のアフィン開被覆にまとめる。
方針：開集合の上限の被覆性と標準チャート射の像の公式を使う。
規約：KST §5、Stacks 0811、添字族の有限性と中心の生成性は不要。
使われ方：一般階数の一定な各指定チャート上の第二段中心を大域で扱う。
-/
def affineBlowupChosenChartCover {R : Type u} [CommRing R] (I : Ideal R)
    {ι : Type v} (a : ι → I) (hcover : (⨆ i, affineBlowupChart I (a i)) = ⊤) :
    (affineBlowup I).AffineOpenCover where
  I₀ := ι
  X i := .of (BlowupChartRing I (a i))
  f i := affineBlowupChartι I (a i)
  idx x := (TopologicalSpace.Opens.mem_iSup.mp (hcover.ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (affineBlowupChartι I _).opensRange
    rw [show (affineBlowupChartι I _).opensRange = affineBlowupChart I _ from
      Proj.opensRange_awayι ..]
    exact (TopologicalSpace.Opens.mem_iSup.mp (hcover.ge (Set.mem_univ x))).choose_spec

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
