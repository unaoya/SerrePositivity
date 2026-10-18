module

public import SerrePositivity.KST.Descent.AlgebraPureTransform
public import SerrePositivity.KST.SchemeLemmas.AffineIdealPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# 代数の純変換の Spec とスキーム論的像

## 概要
純変換商の Spec を実際の閉部分スキームとし、一元局所化のスキーム論的像と同一視する。

## 方針
環の局所化の核と商写像の核を比較し、閉埋め込みの普遍性で標準同型を構成する。

## 規約
スキーム論的像を単なる点集合の閉包で置換しない。

## 使われ方
論文 補題 3.3、公理 (6) の加群純変換とアフィン strict transform の同定。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open SerrePositivity.KST.SchemeLemmas

namespace SerrePositivity.KST.Descent

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] (f : R)

/-- 概要：実際の商代数の Spec（論文 補題 3.3）。
方針：境界ねじれイデアルによる商の Spec を取る。
規約：局所化の Spec とは区別する。
使われ方：平坦化後の strict transform のアフィンモデル。 -/
noncomputable def algebraPureTransformSpec : Scheme.{u} :=
  Spec (.of (algebraPureTransform R B f))

/-- 概要：純変換の Spec の元のアフィン空間への閉包含（論文 補題 3.3）。
方針：実際の商写像を Spec で反変に写す。
規約：元の環 B への射。
使われ方：一元局所化のスキーム論的像の比較。 -/
noncomputable def algebraPureTransformSpecι : algebraPureTransformSpec R B f ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (boundaryTorsionIdeal R B f)))

/-- 概要：純変換の Spec の包含は閉埋め込み（論文 補題 3.3）。
方針：商写像の Spec の既存の閉埋め込み性を使う。
規約：点集合の閉像性だけでない。
使われ方：スキーム論的像の普遍性。 -/
instance algebraPureTransformSpecι_isClosedImmersion :
    IsClosedImmersion (algebraPureTransformSpecι R B f) :=
  IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (boundaryTorsionIdeal R B f)))
    Ideal.Quotient.mk_surjective

/-- 概要：純変換の Spec の基礎環の Spec への構造射（論文 補題 3.3）。
方針：商代数の実際の基礎環からの構造射を Spec で写す。
規約：元の R 代数構造を保持する。
使われ方：加群平坦化からのスキーム射の平坦性。 -/
noncomputable def algebraPureTransformSpecπ : algebraPureTransformSpec R B f ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (algebraPureTransform R B f)))

/-- 概要：純変換加群が平坦なら実際のアフィン純変換の構造射は平坦（論文 補題 3.3）。
方針：商代数の加群との線形同型と Spec の平坦性判定を使う。
規約：スキームの平坦性を実際の射について主張する。
使われ方：blowup チャート上の平坦性を貼り合わせる入力。 -/
theorem algebraPureTransformSpecπ_flat [Module.Flat R (modulePureTransform f B)] :
    Flat (algebraPureTransformSpecπ R B f) :=
  Flat.SpecMap_iff.mpr
    (RingHom.flat_algebraMap_iff.mpr (algebraPureTransform_flat R B f))

/-- 概要：有限代数の実際のアフィン純変換の構造射は有限（論文 補題 3.3）。
方針：商代数の加群としての有限性と Spec の有限性判定を使う。
規約：有限型性だけでなく基礎環上有限であることを要求する。
使われ方：有限平坦な strict transform の局所モデル。 -/
theorem algebraPureTransformSpecπ_isFinite [Module.Finite R B] :
    IsFinite (algebraPureTransformSpecπ R B f) :=
  (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr (algebraPureTransform_finite R B f))

/-- 概要：局所化の Spec の像と純変換閉包含は同じ核イデアル層を持つ（論文 補題 3.3）。
方針：Spec のイデアル対応で実際の二つの環準同型の核を比較する。
規約：イデアル層としての等式であり、台だけの等式ではない。
使われ方：実際のスキーム論的像との標準同型。 -/
theorem algebraPureTransformSpecι_ker :
    (algebraPureTransformSpecι R B f).ker =
      (Spec.map (CommRingCat.ofHom
        (algebraMap B (Localization.Away (algebraMap R B f))))).ker := by
  apply (specIdealEquiv (.of B)).injective
  exact (specIdealEquiv_ker_specMap
    (CommRingCat.ofHom (Ideal.Quotient.mk (boundaryTorsionIdeal R B f)))).trans
      (((Ideal.mk_ker (I := boundaryTorsionIdeal R B f)).trans
        (boundaryTorsionIdeal_eq_ker R B f)).trans
          (specIdealEquiv_ker_specMap (CommRingCat.ofHom
            (algebraMap B (Localization.Away (algebraMap R B f))))).symm)

/-- 概要：一元局所化のスキーム論的像の閉包含の核は純変換閉包含の核（論文 補題 3.3）。
方針：スキーム論的像の閉包含の核の公式と環の核の一致を使う。
規約：実際のスキーム論的像を使う。
使われ方：閉埋め込みの lift による標準同型。 -/
theorem algebraPureTransform_imageι_ker :
    (Spec.map (CommRingCat.ofHom
      (algebraMap B (Localization.Away (algebraMap R B f))))).imageι.ker =
        (algebraPureTransformSpecι R B f).ker := by
  change (_ : (Spec (.of B)).IdealSheafData).subschemeι.ker = _
  rw [Scheme.IdealSheafData.ker_subschemeι]
  exact (algebraPureTransformSpecι_ker R B f).symm

/-- 概要：純変換商の Spec と一元局所化の実際のスキーム論的像の標準同型（論文 補題 3.3）。
方針：同じ核を持つ二つの閉埋め込みの lift を同型と判定する。
規約：同型は元のアフィン空間への閉包含を保つ。
使われ方：加群純変換の平坦性をアフィン strict transform の平坦性へ移す。 -/
noncomputable def algebraPureTransformImageIso :
    algebraPureTransformSpec R B f ≅
      (Spec.map (CommRingCat.ofHom
        (algebraMap B (Localization.Away (algebraMap R B f))))).image := by
  let p := algebraPureTransformSpecι R B f
  let g := Spec.map (CommRingCat.ofHom
    (algebraMap B (Localization.Away (algebraMap R B f))))
  have := IsClosedImmersion.isIso_lift g.imageι p (algebraPureTransform_imageι_ker R B f)
  exact asIso (IsClosedImmersion.lift g.imageι p (algebraPureTransform_imageι_ker R B f).le)

/-- 概要：標準同型は元のアフィン空間への閉包含を保つ（論文 補題 3.3）。
方針：閉埋め込みの lift の指定因子化公式を使う。
規約：同型の hom は実際の lift。
使われ方：チャート上の構造射と元の strict transform の比較。 -/
theorem algebraPureTransformImageIso_hom_imageι :
    (algebraPureTransformImageIso R B f).hom ≫
        (Spec.map (CommRingCat.ofHom
          (algebraMap B (Localization.Away (algebraMap R B f))))).imageι =
      algebraPureTransformSpecι R B f :=
  IsClosedImmersion.lift_fac _ _ _

end SerrePositivity.KST.Descent
