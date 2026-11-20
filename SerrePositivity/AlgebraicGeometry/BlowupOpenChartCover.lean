module

public import SerrePositivity.AlgebraicGeometry.BlowupOpenComparison
public import SerrePositivity.AlgebraicGeometry.ChartGluing

/-!
概要：KST §5、Stacks 080Y・0811 の任意の基底アフィン開被覆に付随する blowup のチャート被覆。
方針：各開集合上の逆像中心の blowup を開逆像と同定し、その標準チャートを合わせる。
規約：切断環の表示を変えず、各元のアフィン被覆の係数環を保持する。
使われ方：第一段の指定チャートに付随する第二段チャートの自由化を大域化する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {X : Scheme.{u}} (K : X.IdealSheafData) (𝒰 : X.AffineOpenCover.{v})

set_option backward.isDefEq.respectTransparency false in
/--
概要：任意の基底アフィン開被覆に付随する局所 blowup の標準チャートは一般 blowup を覆う。
方針：点の基底像を含む被覆成分を選び、開逆像の比較射と標準チャートの被覆性を使う。
規約：KST §5、Stacks 080Y・0811、中心の有限生成性と Noether 性は不要。
使われ方：局所中心の実際の係数環による第二段アフィン開被覆を構成する。
-/
theorem exists_blowupOpenChartι (x : blowup K) :
    ∃ (p : Σ i : 𝒰.I₀, specIdealEquiv (𝒰.X i) (K.comap (𝒰.f i)))
      (z : Spec (.of (BlowupChartRing _ p.2))),
      (affineBlowupChartι _ p.2 ≫ blowupAffineOpenMap (𝒰.f p.1) K) z = x := by
  let i := 𝒰.idx (blowupπ K x)
  have hx : x ∈ Set.range (blowupAffineOpenMap (𝒰.f i) K) := by
    rw [blowupAffineOpenMap_range]
    exact 𝒰.covers (blowupπ K x)
  obtain ⟨y, hy⟩ := hx
  let J := specIdealEquiv (𝒰.X i) (K.comap (𝒰.f i))
  let 𝒱 := affineBlowupChartCover J
  let b : J := 𝒱.idx y
  obtain ⟨z, hz⟩ := 𝒱.covers y
  refine ⟨⟨i, b⟩, z, ?_⟩
  exact (congrArg (blowupAffineOpenMap (𝒰.f i) K) hz).trans hy


set_option backward.isDefEq.respectTransparency false in
/--
概要：任意の基底アフィン開被覆に付随する逆像中心の標準チャートによる blowup のアフィン開被覆。
方針：点ごとの局所標準チャートの存在から添字と被覆証明を選ぶ。
規約：KST §5、Stacks 080Y・0811、添字は元の被覆成分と逆像中心元の組。
使われ方：構成した第二段中心の全局所チャートの性質を被覆に沿って使う。
-/
def blowupOpenChartCover : (blowup K).AffineOpenCover where
  I₀ := Σ i : 𝒰.I₀, specIdealEquiv (𝒰.X i) (K.comap (𝒰.f i))
  X p := .of (BlowupChartRing (specIdealEquiv (𝒰.X p.1) (K.comap (𝒰.f p.1))) p.2)
  f p := affineBlowupChartι _ p.2 ≫ blowupAffineOpenMap (𝒰.f p.1) K
  map_prop _ := by infer_instance
  idx x := (exists_blowupOpenChartι K 𝒰 x).choose
  covers x := (exists_blowupOpenChartι K 𝒰 x).choose_spec

set_option backward.isDefEq.respectTransparency false in
/--
概要：任意の基底被覆に付随する第二段チャートの構造射はチャート環の係数写像で計算できる。
方針：アフィン開 blowup 比較射と標準チャートの基底可換式を合成する。
規約：KST §5、Stacks 080Y・0811、元の基底スキームへの実際の射の等式。
使われ方：各チャートでの自由化を元の基礎環の係数写像と照合する。
-/
@[reassoc] theorem blowupOpenChartCover_base
    (p : Σ i : 𝒰.I₀, specIdealEquiv (𝒰.X i) (K.comap (𝒰.f i))) :
    (blowupOpenChartCover K 𝒰).f p ≫ blowupπ K =
      Spec.map (CommRingCat.ofHom (chartBaseMap _ p.2)) ≫ 𝒰.f p.1 := by
  change (affineBlowupChartι _ p.2 ≫ blowupAffineOpenMap (𝒰.f p.1) K) ≫ _ = _
  rw [Category.assoc, blowupAffineOpenMap_base, ← Category.assoc]
  exact congrArg (fun t => t ≫ 𝒰.f p.1) (affineBlowupChartIso_inv_ι_π _ p.2)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
