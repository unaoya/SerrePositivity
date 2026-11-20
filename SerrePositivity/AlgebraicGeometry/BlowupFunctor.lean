module

public import SerrePositivity.AlgebraicGeometry.BaseChangeMap

/-!
概要：KST §5 のアフィン blowup 比較射の恒等性と合成則。
方針：中心を保つ係数写像の Rees 次数付き関手性と Proj の反変関手性を使う。
規約：像イデアルと標的の中心の等式を明示して中心の表示を固定する。
使われ方：一般スキーム上の blowup の貼り合わせの三重交叉条件。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  (I : Ideal R) (J : Ideal S) (K : Ideal T)

/--
概要：中心の像を同定して与えるアフィン blowup の比較射。
方針：中心の等式から irrelevant ideal の包含を得て Proj の射を構成する。
規約：KST §5、対象の中心は別々のイデアルとして保持する。
使われ方：アフィン開集合の切断環とイデアル層の切断の比較。
-/
def affineBlowupCenterMap (f : R →+* S) (hJ : I.map f = J) :
    affineBlowup J ⟶ affineBlowup I :=
  Proj.map (reesGradedMap I J f hJ.le) (reesGradedMap_irrelevant_le_of_eq I J f hJ)

set_option backward.isDefEq.respectTransparency false in
/--
概要：恒等係数写像による中心を固定した blowup 比較は恒等射。
方針：Rees の次数付き写像の恒等性と Proj の恒等射公式を使う。
規約：KST §5、像イデアルの等式の証明には依存しない。
使われ方：貼り合わせの恒等射条件。
-/
@[simp] theorem affineBlowupCenterMap_id :
    affineBlowupCenterMap I I (RingHom.id R) (by simp) = 𝟙 (affineBlowup I) := by
  unfold affineBlowupCenterMap
  change Proj.map _ _ = 𝟙 (Proj (reesGrade I))
  simp only [reesGradedMap_id]
  exact Proj.map_id

set_option backward.isDefEq.respectTransparency false in
/--
概要：中心の像を同定した blowup 比較射は反変の合成則を満たす。
方針：Rees の次数付き写像の合成則を Proj の合成公式へ移す。
規約：KST §5、三つの中心と二つの係数写像の合成を明示する。
使われ方：アフィン開集合の三重交叉での比較射の両立性。
-/
@[reassoc] theorem affineBlowupCenterMap_comp (f : R →+* S) (hJ : I.map f = J)
    (g : S →+* T) (hK : J.map g = K) :
    affineBlowupCenterMap J K g hK ≫ affineBlowupCenterMap I J f hJ =
      affineBlowupCenterMap I K (g.comp f) (by rw [← Ideal.map_map, hJ, hK]) := by
  unfold affineBlowupCenterMap
  rw [← Proj.map_comp]
  congr 1
  exact reesGradedMap_comp I J f hJ.le K g hK.le

set_option backward.isDefEq.respectTransparency false in
/--
概要：中心を同定した比較射は基礎環の Spec の射と両立する。
方針：Proj の零次成分の構造射の自然性と定数係数の保存を使う。
規約：KST §5、中心の等式の証明には依存しない。
使われ方：アフィン開集合上の blowup の構造射の貼り合わせ。
-/
@[reassoc] theorem affineBlowupCenterMap_base (f : R →+* S) (hJ : I.map f = J) :
    affineBlowupCenterMap I J f hJ ≫ affineBlowupπ I =
      affineBlowupπ J ≫ Spec.map (CommRingCat.ofHom f) := by
  unfold affineBlowupCenterMap affineBlowupπ
  rw [← Category.assoc, proj_map_toSpecZero]
  simp only [Category.assoc, ← Spec.map_comp]
  congr 2
  ext r : 2
  apply Subtype.ext
  apply Subtype.ext
  change (Polynomial.C r).map f = Polynomial.C (f r)
  exact Polynomial.map_C f

/--
概要：像中心をそのまま用いた中心比較射は自然な基底比較射と一致する。
方針：同じ Rees 次数付き写像と irrelevant ideal の包含を使う。
規約：KST §5、等式証明の違いは証明無関係性で吸収する。
使われ方：局所化で構成した同型と中心を同定した比較の接続。
-/
theorem affineBlowupCenterMap_eq_baseMap (f : R →+* S) :
    affineBlowupCenterMap I (I.map f) f rfl = affineBlowupBaseMap I f := rfl

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
