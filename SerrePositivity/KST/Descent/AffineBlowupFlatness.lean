module

public import SerrePositivity.KST.Descent.AffinePresentation
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupCharts

/-!
# アフィン基底の実際の全標準チャートによる strict transform の平坦性

## 概要
全切断環の実際の blowup チャートの純変換が平坦なら、元の strict transform の構造射は平坦。

## 方針
全体のアフィンモデルから実際の標準チャートの開被覆を構成し、係数射の公式を適用する。

## 規約
元の基底と全切断環の Spec を同一視しない。準コンパクト性とアフィン表示の可換式を明示する。

## 使われ方
論文 補題 3.3、公理 (6) の加群平坦化中心から実際の global な平坦化への接続。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open SerrePositivity.AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {Y : Scheme.{u}} [IsAffine Y] (J : Y.IdealSheafData)

set_option backward.isDefEq.respectTransparency false in
/-- 概要：全体のアフィンモデルから元の blowup への実際の標準射は全射（論文 補題 3.3）。
方針：標準射の像が全体の逆像に一致することを使う。
規約：中心の有限生成性は不要。
使われ方：全切断環の全標準チャートを元の blowup の開被覆にする。 -/
theorem blowupTopModel_surjective :
    Function.Surjective (blowupAffineι J ⟨⊤, isAffineOpen_top Y⟩) := by
  rw [← Set.range_eq_univ, blowupAffineι_range]
  simp

/-- 概要：全切断環の実際の全標準チャートによる元の blowup のアフィン開被覆（補題 3.3）。
方針：全体のアフィンモデルへの点の持ち上げとその標準チャート被覆を合成する。
規約：各チャートの射は既存の実際の blowupChartι。
使われ方：全てのチャートの加群平坦化の入力を元の構造射に適用する。 -/
noncomputable def blowupTopChartCover : (blowup J).AffineOpenCover where
  I₀ := J.ideal ⟨⊤, isAffineOpen_top Y⟩
  X a := .of (BlowupChartRing (J.ideal ⟨⊤, isAffineOpen_top Y⟩) a)
  f a := blowupChartι J ⟨⊤, isAffineOpen_top Y⟩ a
  idx x := (affineBlowupChartCover (J.ideal ⟨⊤, isAffineOpen_top Y⟩)).idx
    ((blowupTopModel_surjective J x).choose)
  covers x := by
    let y := (blowupTopModel_surjective J x).choose
    obtain ⟨z, hz⟩ := (affineBlowupChartCover (J.ideal ⟨⊤, isAffineOpen_top Y⟩)).covers y
    exact ⟨z, (congrArg (blowupAffineι J ⟨⊤, isAffineOpen_top Y⟩) hz).trans
      (blowupTopModel_surjective J x).choose_spec⟩

variable {X : Scheme.{u}} (f : X ⟶ Y) (B : Type u) [CommRing B] [Algebra Γ(Y, ⊤) B]
  (eX : Spec (.of B) ≅ X)
  (hf : eX.hom ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) B)) ≫
    (affineTopPresentation Y).hom)

include hf in
set_option backward.isDefEq.respectTransparency false in
/-- 概要：実際の全標準チャートの加群純変換の平坦性から global strict transform の平坦性（補題 3.3）。
方針：標準チャートの係数射との可換式をテンソル積モデルに適用し、実際の開被覆で貼り合わせる。
規約：境界元は Γ(Y,⊤) の同じ元で、元のアフィン表示の同型 eX を保持する。
使われ方：実際の有限加群の平坦化中心をスキームの平坦化の結論にする。 -/
theorem strictTransform_flat_of_topChart_pureTransforms (r : Γ(Y, ⊤))
    [QuasiCompact (strictTransformOpen f (Y.basicOpen r) J).ι]
    (hflat : ∀ a : J.ideal ⟨⊤, isAffineOpen_top Y⟩,
      letI : Algebra Γ(Y, ⊤) (BlowupChartRing (J.ideal ⟨⊤, isAffineOpen_top Y⟩) a) :=
        (chartBaseMap (J.ideal ⟨⊤, isAffineOpen_top Y⟩) a).toAlgebra
      Module.Flat (BlowupChartRing (J.ideal ⟨⊤, isAffineOpen_top Y⟩) a)
        (modulePureTransform (chartBaseMap (J.ideal ⟨⊤, isAffineOpen_top Y⟩) a r)
          (BlowupChartRing (J.ideal ⟨⊤, isAffineOpen_top Y⟩) a ⊗[Γ(Y, ⊤)] B))) :
    Flat (strictTransformπ f (Y.basicOpen r) J) := by
  have : IsZariskiLocalAtTarget @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{u}) (Q := @RingHom.Flat)
  apply IsZariskiLocalAtTarget.of_openCover (P := @Flat) (blowupTopChartCover J).openCover
  intro a
  let A := BlowupChartRing (J.ideal ⟨⊤, isAffineOpen_top Y⟩) a
  let : Algebra Γ(Y, ⊤) A := (chartBaseMap (J.ideal ⟨⊤, isAffineOpen_top Y⟩) a).toAlgebra
  have : Module.Flat A
      (modulePureTransform (chartBaseMap (J.ideal ⟨⊤, isAffineOpen_top Y⟩) a r)
        (A ⊗[Γ(Y, ⊤)] B)) := hflat a
  exact strictTransform_chart_flat_of_affineModel Γ(Y, ⊤) B A f eX (affineTopPresentation Y)
    hf J (blowupChartι J ⟨⊤, isAffineOpen_top Y⟩ a)
    (blowupChartι_π J ⟨⊤, isAffineOpen_top Y⟩ a)
    (Y.basicOpen r) r (affineTopPresentation_preimage_basicOpen Y r)

end SerrePositivity.KST.Descent
