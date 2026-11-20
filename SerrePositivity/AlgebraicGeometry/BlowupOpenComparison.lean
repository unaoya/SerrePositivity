module

public import SerrePositivity.AlgebraicGeometry.BlowupAffineOpenMap
public import SerrePositivity.AlgebraicGeometry.BlowupRingEquiv
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupAffine
public import SerrePositivity.AlgebraicGeometry.OpenCenterExtension
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
概要：KST §5、Stacks 080Y の任意のアフィン開基底変更による blowup の比較同型。
方針：チャート環と開像の切断環の同型により係数比較を同型とし、構造射の開逆像と同定する。
規約：実際の比較射とその像の等式を保持する。
使われ方：局所中心の延長とアフィン支配射の大域化。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {X : Scheme.{u}} {A : CommRingCat.{u}} (j : Spec A ⟶ X) [IsOpenImmersion j]
  (K : X.IdealSheafData)

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン開像の係数環準同型は全単射。
方針：その Spec が構成済みの同型の順射であることを使う。
規約：KST §5、Stacks 080Y、切断環の表示の同一視はしない。
使われ方：blowup の係数比較射を同型と判定する。
-/
theorem affineOpenImageRingMap_bijective : Function.Bijective (affineOpenImageRingMap j).hom := by
  apply isIso_SpecMap_iff.mp
  change IsIso (Spec.map (Spec.preimage (affineOpenImageSpecIso j).hom))
  rw [Spec.map_preimage]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
概要：任意のアフィン開チャートの中心比較射は同型。
方針：係数環準同型を実際の環同型に束ね、中心を保つ環同型の blowup 同型を使う。
規約：KST §5、Stacks 080Y、有限生成性は不要。
使われ方：一般 blowup の任意のアフィン開基底変更への比較。
-/
theorem affineOpenImageBlowupCenterMap_isIso :
    IsIso (affineBlowupCenterMap (K.ideal (affineOpenImage j))
      (specIdealEquiv A (K.comap j)) (affineOpenImageRingMap j).hom
      (affineOpenImageRingMap_center j K)) := by
  let e := RingEquiv.ofBijective (affineOpenImageRingMap j).hom (affineOpenImageRingMap_bijective j)
  exact (affineBlowupRingEquivIso (K.ideal (affineOpenImage j))
    (specIdealEquiv A (K.comap j)) e (affineOpenImageRingMap_center j K)).isIso_hom

set_option backward.isDefEq.respectTransparency false in
/--
概要：任意のアフィン開チャート上の blowup 比較射は開埋め込み。
方針：係数比較の同型と局所モデルの標準開埋め込みを合成する。
規約：KST §5、Stacks 080Y、実際の比較射についての性質。
使われ方：構造射の開逆像との同型を作る。
-/
instance blowupAffineOpenMap_isOpenImmersion : IsOpenImmersion (blowupAffineOpenMap j K) := by
  have := affineOpenImageBlowupCenterMap_isIso j K
  unfold blowupAffineOpenMap
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
概要：任意のアフィン開チャートの blowup 比較射の像は基底の開像の逆像。
方針：係数比較射の全射性と標準局所モデルの像の公式を使う。
規約：KST §5、Stacks 080Y、点集合の像の等式。
使われ方：アフィン開基底変更の実際の同型。
-/
theorem blowupAffineOpenMap_range :
    Set.range (blowupAffineOpenMap j K) = (blowupπ K ⁻¹ᵁ j.opensRange).carrier := by
  have := affineOpenImageBlowupCenterMap_isIso j K
  let c := affineBlowupCenterMap (K.ideal (affineOpenImage j))
    (specIdealEquiv A (K.comap j)) (affineOpenImageRingMap j).hom
    (affineOpenImageRingMap_center j K)
  have hsurj : Function.Surjective c := c.homeomorph.surjective
  change Set.range (c ≫ blowupAffineι K (affineOpenImage j)) = _
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ]
  exact blowupAffineι_range K (affineOpenImage j)

/--
概要：任意のアフィン開チャート上の blowup は一般 blowup の対応する開逆像と同型。
方針：開埋め込みで像が一致する二つの射を比較する。
規約：KST §5、Stacks 080Y、中心は実際の逆像イデアル層に対応する。
使われ方：局所中心を全体へ延長した後のアフィン支配射の利用。
-/
def blowupOpenIso : affineBlowup (specIdealEquiv A (K.comap j)) ≅
    (blowupπ K ⁻¹ᵁ j.opensRange).toScheme :=
  IsOpenImmersion.isoOfRangeEq (blowupAffineOpenMap j K) (blowupπ K ⁻¹ᵁ j.opensRange).ι
    ((blowupAffineOpenMap_range j K).trans (Scheme.Opens.range_ι _).symm)

/--
概要：アフィン開比較同型は一般 blowup への開包含と元の比較射を保つ。
方針：開像の一致による同型の因子化式を使う。
規約：KST §5、Stacks 080Y、同型の順方向を使う。
使われ方：大域の構造射と局所的な支配射の交換式。
-/
@[reassoc] theorem blowupOpenIso_hom_ι :
    (blowupOpenIso j K).hom ≫ (blowupπ K ⁻¹ᵁ j.opensRange).ι = blowupAffineOpenMap j K :=
  IsOpenImmersion.isoOfRangeEq_hom_fac ..

set_option backward.isDefEq.respectTransparency false in
/--
概要：開逆像からアフィン blowup へ戻る同型も基底の構造射を保つ。
方針：同型の順射の因子化式と比較射の基底交換式を使う。
規約：KST §5、Stacks 080Y、同型の逆方向の構造射公式。
使われ方：大域共通細分から局所支配射へ進む。
-/
@[reassoc] theorem blowupOpenIso_inv_base :
    (blowupOpenIso j K).inv ≫ affineBlowupπ (specIdealEquiv A (K.comap j)) ≫ j =
      (blowupπ K ⁻¹ᵁ j.opensRange).ι ≫ blowupπ K := by
  rw [← blowupAffineOpenMap_base, ← blowupOpenIso_hom_ι_assoc, Iso.inv_hom_id_assoc]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
