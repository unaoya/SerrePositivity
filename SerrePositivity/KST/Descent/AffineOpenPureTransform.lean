module

public import SerrePositivity.KST.Descent.AffinePureTransform

/-!
# 基本開のスキーム論的像としてのアフィン純変換

## 概要
純変換商の Spec を基本開 D(f) の実際のスキーム論的像と、閉包含を保つ同型で結ぶ。

## 方針
基本開と一元局所化の Spec の標準同型を使い、核イデアル層を比較する。

## 規約
スキーム論的像の構造層を保持する。任意の blowup チャートとの比較は別工程。

## 使われ方
論文 補題 3.3、公理 (6) の加群平坦化からアフィン strict transform の平坦性への接続。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open SerrePositivity.KST.SchemeLemmas

namespace SerrePositivity.KST.Descent

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] (f : R)

/-- 概要：境界元の基本開を元のアフィン空間の開部分とする（論文 補題 3.3）。
方針：基礎環の元の B での像による基本開を取る。
規約：R の基本開ではなく、その逆像に対応する B の基本開。
使われ方：スキーム論的像で定義した strict transform のアフィンモデル。 -/
def algebraBoundaryOpen : (Spec (.of B)).Opens :=
  PrimeSpectrum.basicOpen (algebraMap R B f)

/-- 概要：基本開のスキーム論的像から基礎環への実際の構造射（論文 補題 3.3）。
方針：像の閉包含と元の代数の構造射を合成する。
規約：前層の値域の射ではなくスキームの射。
使われ方：blowup チャート上の平坦化の結論。 -/
noncomputable def algebraBoundaryImageπ : (algebraBoundaryOpen R B f).ι.image ⟶ Spec (.of R) :=
  (algebraBoundaryOpen R B f).ι.imageι ≫ Spec.map (CommRingCat.ofHom (algebraMap R B))

/-- 概要：基本開の閉包含の核は純変換商の閉包含の核（論文 補題 3.3）。
方針：基本開と局所化の Spec の同型を通して核を比較する。
規約：核は実際のイデアル層として比較する。
使われ方：商の Spec と基本開のスキーム論的像との標準同型。 -/
theorem algebraBoundaryOpen_ker :
    (algebraBoundaryOpen R B f).ι.ker = (algebraPureTransformSpecι R B f).ker := by
  have h := congrArg Scheme.Hom.ker
    (basicOpenIsoSpecAway_hom_SpecMap (R := .of B) (algebraMap R B f))
  exact h.symm.trans
    ((Scheme.Hom.ker_comp_of_isIso
      (basicOpenIsoSpecAway (R := .of B) (algebraMap R B f)).hom _).trans
      (algebraPureTransformSpecι_ker R B f).symm)

/-- 概要：純変換商の Spec と基本開の実際のスキーム論的像の標準同型（論文 補題 3.3）。
方針：同じ核イデアル層を持つ閉包含の間の lift を同型にする。
規約：元のアフィン空間への射を保持する。
使われ方：加群の純変換と開部分のスキーム論的閉包の同定。 -/
noncomputable def algebraPureTransformBasicOpenImageIso :
    algebraPureTransformSpec R B f ≅ (algebraBoundaryOpen R B f).ι.image := by
  have h : (algebraBoundaryOpen R B f).ι.imageι.ker =
      (algebraPureTransformSpecι R B f).ker := by
    change (_ : (Spec (.of B)).IdealSheafData).subschemeι.ker = _
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact algebraBoundaryOpen_ker R B f
  have := IsClosedImmersion.isIso_lift (algebraBoundaryOpen R B f).ι.imageι
    (algebraPureTransformSpecι R B f) h
  exact asIso (IsClosedImmersion.lift (algebraBoundaryOpen R B f).ι.imageι
    (algebraPureTransformSpecι R B f) h.le)

/-- 概要：基本開のスキーム論的像との同型は閉包含を保つ（論文 補題 3.3）。
方針：閉埋め込みの lift の因子化公式を使う。
規約：同型の hom は指定された lift。
使われ方：基礎環への構造射の可換性。 -/
theorem algebraPureTransformBasicOpenImageIso_hom_imageι :
    (algebraPureTransformBasicOpenImageIso R B f).hom ≫
        (algebraBoundaryOpen R B f).ι.imageι = algebraPureTransformSpecι R B f :=
  IsClosedImmersion.lift_fac _ _ _

/-- 概要：アフィン純変換の二つの構造射は元の基礎環上で可換（論文 補題 3.3）。
方針：商の代数構造の構造写像と Spec の反変合成を使う。
規約：指定された閉包含と構造射の等式。
使われ方：基本開のスキーム論的像の平坦性の移送。 -/
theorem algebraPureTransformSpec_square :
    algebraPureTransformSpecι R B f ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)) = algebraPureTransformSpecπ R B f := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- 概要：基本開のスキーム論的像との同型は基礎環への構造射を保つ（論文 補題 3.3）。
方針：閉包含を保つ式と二つの構造射の可換式を合成する。
規約：構造射は基本開のスキーム論的像の実際の閉包含から作る。
使われ方：加群平坦化を実際の像の平坦性に移す。 -/
theorem algebraPureTransformBasicOpenImageIso_hom_structure :
    (algebraPureTransformBasicOpenImageIso R B f).hom ≫
        ((algebraBoundaryOpen R B f).ι.imageι ≫
          Spec.map (CommRingCat.ofHom (algebraMap R B))) = algebraPureTransformSpecπ R B f :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (algebraPureTransformBasicOpenImageIso_hom_imageι R B f)).trans
      (algebraPureTransformSpec_square R B f))

/-- 概要：加群純変換が平坦なら基本開の実際のスキーム論的像の構造射も平坦（補題 3.3）。
方針：商の Spec との基礎環上の同型で実際のスキームの平坦性を移す。
規約：単なる点集合の閉包の平坦性ではない。
使われ方：strict transform のアフィンチャートでの平坦性。 -/
theorem algebraBoundaryOpen_image_flat [Module.Flat R (_root_.SerrePositivity.AlgebraicGeometry.modulePureTransform f B)] :
    Flat ((algebraBoundaryOpen R B f).ι.imageι ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
  let e := algebraPureTransformBasicOpenImageIso R B f
  have hp : Flat (algebraPureTransformSpecπ R B f) := algebraPureTransformSpecπ_flat R B f
  have h : e.inv ≫ algebraPureTransformSpecπ R B f =
      (algebraBoundaryOpen R B f).ι.imageι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
    e.inv_comp_eq.mpr (algebraPureTransformBasicOpenImageIso_hom_structure R B f).symm
  have : Flat (e.inv ≫ algebraPureTransformSpecπ R B f) := inferInstance
  exact h ▸ this

/-- 概要：有限代数の基本開のスキーム論的像の構造射は有限（論文 補題 3.3）。
方針：有限な純変換商の Spec と構造射を保つ同型で有限性を移す。
規約：基礎環上の加群としての有限性を要求する。
使われ方：平坦化する strict transform の有限性のアフィンモデル。 -/
theorem algebraBoundaryOpen_image_isFinite [Module.Finite R B] :
    IsFinite ((algebraBoundaryOpen R B f).ι.imageι ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
  let e := algebraPureTransformBasicOpenImageIso R B f
  have hp : IsFinite (algebraPureTransformSpecπ R B f) := algebraPureTransformSpecπ_isFinite R B f
  have h : e.inv ≫ algebraPureTransformSpecπ R B f =
      (algebraBoundaryOpen R B f).ι.imageι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
    e.inv_comp_eq.mpr (algebraPureTransformBasicOpenImageIso_hom_structure R B f).symm
  have : IsFinite (e.inv ≫ algebraPureTransformSpecπ R B f) := inferInstance
  exact h ▸ this

end SerrePositivity.KST.Descent
