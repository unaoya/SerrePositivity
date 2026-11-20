module

public import SerrePositivity.AlgebraicGeometry.AffineModelLocalization

/-!
概要：KST §5 の任意のアフィン開包含に沿う blowup 局所モデルの開埋め込み。
方針：両方のアフィン開集合で基本開となる共通近傍を用いて局所化の結果を適用する。
規約：基礎スキームの分離性は仮定しない。
使われ方：アフィン局所モデルの図式を開埋め込みの図式として貼り合わせる。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {X : Scheme.{u}} (I : X.IdealSheafData)

set_option backward.isDefEq.respectTransparency false in
/--
概要：局所モデルの構造射の像は対応するアフィン開集合に含まれる。
方針：構造射がアフィン開包含を通ることを使う。
規約：KST §5、基礎スキーム上の点の所属として述べる。
使われ方：共通の基本開近傍を選ぶ。
-/
theorem affineBlowupModelToBase_mem (U : X.affineOpens) (x : affineBlowupModel I U) :
    affineBlowupModelToBase I U x ∈ U.1 := by
  exact (affineBlowupModelπ I U x).2

set_option backward.isDefEq.respectTransparency false in
/--
概要：包含 U ⊆ V の局所モデルの各点は、両方で基本開となる共通モデルから来る。
方針：基底の共通基本開近傍と、基本開集合へのモデル比較の像の公式を用いる。
規約：KST §5、共通モデルの両方向の比較は開埋め込み。
使われ方：任意のアフィン開包含に沿う比較の単射性と局所開埋め込み性。
-/
theorem affineBlowupModelMap_common_basic {U V : X.affineOpens} (h : U ≤ V)
    (x : affineBlowupModel I U) :
    ∃ (W : X.affineOpens) (hWU : W ≤ U) (hWV : W ≤ V),
      IsOpenImmersion (affineBlowupModelMap I hWU) ∧
      IsOpenImmersion (affineBlowupModelMap I hWV) ∧
      Set.range (affineBlowupModelMap I hWU) =
        (affineBlowupModelToBase I U ⁻¹ᵁ W.1).carrier ∧
      ∃ w : affineBlowupModel I W, affineBlowupModelMap I hWU w = x := by
  have hxU := affineBlowupModelToBase_mem I U x
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2
    (affineBlowupModelToBase I U x) ⟨hxU, h hxU⟩
  let W := X.affineBasicOpen f
  let hWU : W ≤ U := X.affineBasicOpen_le f
  let hWV : W ≤ V := hWU.trans h
  refine ⟨W, hWU, hWV, inferInstance, ?_, affineBlowupModelMap_basicOpen_range I f, ?_⟩
  · exact affineBlowupModelMap_isOpenImmersion_of_eq_basicOpen I hWV g (Subtype.ext hfg)
  · have hx : x ∈ (affineBlowupModelToBase I U ⁻¹ᵁ X.basicOpen f).carrier := hxf
    rw [← affineBlowupModelMap_basicOpen_range I f] at hx
    exact hx

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン開包含に沿う blowup 局所モデルの比較は点集合上で単射。
方針：一方の点の共通基本開近傍へ両点を持ち上げ、標的側の開埋め込みで比較する。
規約：KST §5、被約性や基礎スキームの分離性は仮定しない。
使われ方：比較射の開埋め込み性の大域的な単射条件。
-/
theorem affineBlowupModelMap_injective {U V : X.affineOpens} (h : U ≤ V) :
    Function.Injective (affineBlowupModelMap I h) := by
  intro x y hxy
  obtain ⟨W, hWU, hWV, hWUo, hWVo, hrange, w, hw⟩ :=
    affineBlowupModelMap_common_basic I h x
  have := hWUo
  have := hWVo
  have hbase : affineBlowupModelToBase I U x = affineBlowupModelToBase I U y := by
    calc
      _ = (affineBlowupModelMap I h ≫ affineBlowupModelToBase I V) x := by
        rw [affineBlowupModelMap_toBase]
      _ = (affineBlowupModelMap I h ≫ affineBlowupModelToBase I V) y :=
        congrArg (affineBlowupModelToBase I V) hxy
      _ = _ := by rw [affineBlowupModelMap_toBase]
  have hxW : x ∈ (affineBlowupModelToBase I U ⁻¹ᵁ W.1).carrier := by
    rw [← hrange]
    exact ⟨w, hw⟩
  have hyW : y ∈ (affineBlowupModelToBase I U ⁻¹ᵁ W.1).carrier := by
    change affineBlowupModelToBase I U y ∈ W.1
    rw [← hbase]
    exact hxW
  rw [← hrange] at hyW
  obtain ⟨w', hw'⟩ := hyW
  have hcomp : affineBlowupModelMap I hWU ≫ affineBlowupModelMap I h =
      affineBlowupModelMap I hWV := affineBlowupModelMap_comp I hWU h
  have hww : w = w' := by
    apply (affineBlowupModelMap I hWV).isOpenEmbedding.injective
    calc
      _ = (affineBlowupModelMap I hWU ≫ affineBlowupModelMap I h) w := by rw [hcomp]
      _ = affineBlowupModelMap I h x := congrArg (affineBlowupModelMap I h) hw
      _ = affineBlowupModelMap I h y := hxy
      _ = (affineBlowupModelMap I hWU ≫ affineBlowupModelMap I h) w' :=
        (congrArg (affineBlowupModelMap I h) hw').symm
      _ = _ := by rw [hcomp]
  exact hw.symm.trans ((congrArg (affineBlowupModelMap I hWU) hww).trans hw')

set_option backward.isDefEq.respectTransparency false in
/--
概要：任意のアフィン開包含に沿う blowup 局所モデルの比較射は開埋め込み。
方針：点集合上の単射性と、共通基本開近傍上の開埋め込み性を合わせる。
規約：KST §5、基礎スキームは任意。
使われ方：一般スキーム上の blowup を局所モデルの開貼り合わせで構成する。
-/
instance affineBlowupModelMap_isOpenImmersion {U V : X.affineOpens} (h : U ≤ V) :
    IsOpenImmersion (affineBlowupModelMap I h) := by
  apply IsOpenImmersion.of_forall_source_exists _ (affineBlowupModelMap_injective I h)
  intro x
  obtain ⟨W, hWU, hWV, hWUo, hWVo, _, w, hw⟩ :=
    affineBlowupModelMap_common_basic I h x
  refine ⟨affineBlowupModel I W, affineBlowupModelMap I hWU, hWUo, ⟨w, hw⟩, ?_⟩
  rw [affineBlowupModelMap_comp]
  exact hWVo

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
