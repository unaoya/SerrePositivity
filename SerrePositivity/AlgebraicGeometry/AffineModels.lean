module

public import SerrePositivity.AlgebraicGeometry.BlowupRingEquiv
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
概要：KST §5 の一般スキーム上の blowup のアフィン局所モデルと比較図式。
方針：イデアル層の各アフィン開集合上の切断を中心とし、制限写像で比較する。
規約：Mathlib の IdealSheafData の実際の切断イデアルを用いる。
使われ方：局所 blowup を貼り合わせるための図式。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {X : Scheme.{u}} (I : X.IdealSheafData)

/--
概要：イデアル層のアフィン開集合上の blowup 局所モデル。
方針：切断環と切断イデアルの Rees 代数の Proj を取る。
規約：KST §5、局所モデルの基底は各アフィン開集合の切断環の Spec。
使われ方：一般スキーム上の blowup の貼り合わせの対象。
-/
def affineBlowupModel (U : X.affineOpens) : Scheme := affineBlowup (I.ideal U)

/--
概要：アフィン開集合の包含による切断環の制限準同型。
方針：構造層の前層の制限写像を使う。
規約：KST §5、U ⊆ V に対し Γ(V) から Γ(U) へ向かう。
使われ方：局所 blowup の中心比較射の係数写像。
-/
def affineModelRestriction {U V : X.affineOpens} (h : U ≤ V) :
    Γ(X, V.1) →+* Γ(X, U.1) := (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom

/--
概要：アフィン局所 blowup モデル間の包含に沿う比較射。
方針：イデアル層の制限による像イデアルの等式を中心比較射に渡す。
規約：KST §5、U ⊆ V に対して Bl(U) から Bl(V) へ向かう。
使われ方：一般スキーム上での比較図式。
-/
def affineBlowupModelMap {U V : X.affineOpens} (h : U ≤ V) :
    affineBlowupModel I U ⟶ affineBlowupModel I V :=
  affineBlowupCenterMap (I.ideal V) (I.ideal U) (affineModelRestriction h) (I.map_ideal h)

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン局所モデルの恒等包含の比較射は恒等射。
方針：前層の恒等射の保存と中心比較の恒等射条件を使う。
規約：KST §5、包含の証明には依存しない。
使われ方：貼り合わせ図式の恒等射条件。
-/
@[simp] theorem affineBlowupModelMap_refl (U : X.affineOpens) :
    affineBlowupModelMap I (show U ≤ U from le_rfl) = 𝟙 _ := by
  unfold affineBlowupModelMap affineModelRestriction
  change _ = 𝟙 (affineBlowup (I.ideal U))
  have hres : (X.presheaf.map (homOfLE (X := X.Opens)
      (show U ≤ U from le_rfl)).op).hom = RingHom.id _ := by
    rw [show (homOfLE (X := X.Opens) (show U ≤ U from le_rfl)).op =
      𝟙 (Opposite.op U.1) from rfl,
      X.presheaf.map_id]
    rfl
  simpa only [hres] using affineBlowupCenterMap_id (I.ideal U)

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン局所モデルの比較射は包含の合成と両立する。
方針：前層の制限の合成則と blowup 中心比較の反変合成則を用いる。
規約：KST §5、U ⊆ V ⊆ W の三重比較。
使われ方：一般スキーム上の貼り合わせのコサイクル条件。
-/
@[reassoc] theorem affineBlowupModelMap_comp {U V W : X.affineOpens}
    (hUV : U ≤ V) (hVW : V ≤ W) :
    affineBlowupModelMap I hUV ≫ affineBlowupModelMap I hVW =
      affineBlowupModelMap I (hUV.trans hVW) := by
  unfold affineBlowupModelMap
  rw [affineBlowupCenterMap_comp]
  have hres : (affineModelRestriction hUV).comp (affineModelRestriction hVW) =
      affineModelRestriction (hUV.trans hVW) := by
    change (X.presheaf.map (homOfLE (X := X.Opens) hVW).op ≫
      X.presheaf.map (homOfLE (X := X.Opens) hUV).op).hom = _
    rw [← X.presheaf.map_comp]
    rfl
  simp only [hres]

/--
概要：全てのアフィン開集合上の blowup 局所モデルからなる比較図式。
方針：包含に沿う中心比較射とその恒等性・合成則を束ねる。
規約：KST §5、添字圏はアフィン開集合の順序圏。
使われ方：一般スキーム上での blowup の貼り合わせ。
-/
def affineBlowupDiagram : X.affineOpens ⥤ Scheme where
  obj U := affineBlowupModel I U
  map h := affineBlowupModelMap I (leOfHom h)
  map_id U := affineBlowupModelMap_refl I U
  map_comp h g := (affineBlowupModelMap_comp I (leOfHom h) (leOfHom g)).symm

/--
概要：各 blowup 局所モデルから対応するアフィン開部分スキームへの構造射。
方針：切断環の Spec 上の構造射をアフィン開集合との自然同型で移す。
規約：KST §5、一般スキーム X への射はさらに開包含を合成する。
使われ方：局所 blowup の構造射の貼り合わせ。
-/
def affineBlowupModelπ (U : X.affineOpens) : affineBlowupModel I U ⟶ U.1.toScheme :=
  affineBlowupπ (I.ideal U) ≫ U.2.isoSpec.inv

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン局所モデルの比較射はアフィン開集合上の構造射と両立する。
方針：中心比較射の基底両立性とアフィン切断環の自然性を合成する。
規約：KST §5、包含 U ⊆ V の上の交換式。
使われ方：一般スキーム上の構造射の貼り合わせ。
-/
@[reassoc] theorem affineBlowupModelMap_π {U V : X.affineOpens} (h : U ≤ V) :
    affineBlowupModelMap I h ≫ affineBlowupModelπ I V =
      affineBlowupModelπ I U ≫ X.homOfLE h := by
  unfold affineBlowupModelMap affineBlowupModelπ
  rw [← Category.assoc, affineBlowupCenterMap_base]
  simp only [Category.assoc]
  congr 1
  rw [Iso.eq_inv_comp, IsAffineOpen.isoSpec_hom]
  unfold affineModelRestriction
  rw [CommRingCat.ofHom_hom]
  erw [Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc U.1 V.1 h]
  rw [← IsAffineOpen.isoSpec_hom V.2, Iso.hom_inv_id, Category.comp_id]

/--
概要：各アフィン blowup 局所モデルから一般スキーム X への構造射。
方針：アフィン開部分スキーム上の構造射に開包含を合成する。
規約：KST §5、全ての局所モデルで基底を X にそろえる。
使われ方：一般スキーム上の blowup の構造射の貼り合わせ。
-/
def affineBlowupModelToBase (U : X.affineOpens) : affineBlowupModel I U ⟶ X :=
  affineBlowupModelπ I U ≫ U.1.ι

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン局所モデルの比較射は X 上の射。
方針：アフィン開集合上の交換式に開包含を合成する。
規約：KST §5、U ⊆ V の比較について述べる。
使われ方：構造射を大域化するための自然性。
-/
@[reassoc] theorem affineBlowupModelMap_toBase {U V : X.affineOpens} (h : U ≤ V) :
    affineBlowupModelMap I h ≫ affineBlowupModelToBase I V = affineBlowupModelToBase I U := by
  unfold affineBlowupModelToBase
  rw [affineBlowupModelMap_π_assoc, X.homOfLE_ι]

set_option backward.isDefEq.respectTransparency false in
/--
概要：局所モデルの構造射による基本開集合の逆像は切断環の基本開集合の逆像。
方針：アフィン開集合の切断環の Spec との自然同型を通して基本開集合を比較する。
規約：KST §5、基本開集合は元のスキーム X 上のもの。
使われ方：局所モデルの包含の像と開被覆の計算。
-/
theorem affineBlowupModelToBase_preimage_basicOpen (V : X.affineOpens) (f : Γ(X, V.1)) :
    affineBlowupModelToBase I V ⁻¹ᵁ X.basicOpen f =
      affineBlowupπ (I.ideal V) ⁻¹ᵁ PrimeSpectrum.basicOpen f := by
  unfold affineBlowupModelToBase affineBlowupModelπ
  rw [Category.assoc, IsAffineOpen.isoSpec_inv_ι, Scheme.Hom.comp_preimage,
    V.2.fromSpec_preimage_basicOpen]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
