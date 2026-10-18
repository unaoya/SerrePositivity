module

public import SerrePositivity.KST.Descent.SchemeActionTransport
public import SerrePositivity.KST.Descent.AffineTensorSquare

/-!
# 任意のアフィン基底変更への幾何的推移性の帰結

## 概要
元の環論的な幾何的推移性から、実際のアフィン基底変更の点のファイバーの推移性を導く。

## 方針
基底の座標環へ係数拡大し、テンソル積モデルの作用を二射影を保つ同型で移す。

## 規約
基底変更側の作用は自明。通常の点の推移性だけからの任意の底変換の保存は使わない。

## 使われ方
論文 補題 3.2 の実際の Čech 各段への幾何的推移性の供給。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace SerrePositivity.KST.Descent

variable {A T G : Type u} [CommRing A] [CommRing T] [Algebra A T]
  [Group G] [MulSemiringAction G T] [SMulCommClass G A T]
variable {Z : Scheme.{u}} (i : Z ⟶ Spec (.of A))

/-- 概要：実際のアフィン基底変更の始域への指定作用（論文 補題 3.2）。
方針：Spec T の作用を引き戻し、基底変更側の Z は固定する。
規約：実際の指定引き戻しと元の Spec の作用を使う。
使われ方：Čech 各段の点の推移性の比較先。 -/
noncomputable def affineSchemeBaseChangeAction :
    G →* Aut (pullback (Spec.map (CommRingCat.ofHom (algebraMap A T))) i) :=
  pullbackAction _ i (specAction (G := G)) 1 1
    (fun g ↦ (specAction_over_base g).trans (Category.comp_id _).symm)
    (fun _ ↦ (Category.id_comp i).trans (Category.comp_id i).symm)

/-- 概要：座標環の表示を持つ実際の基底変更の点の推移性（論文 補題 3.2）。
方針：テンソル積の Cartesian 正方形を基底の指定同型で移し、作用を同変に比較する。
規約：基底の有限型性・Noether 性・群の有限性はこの推移性には不要。
使われ方：任意のアフィン基底の座標環表示への適用。 -/
theorem affineSchemeBaseChange_transitive_of_coordinates
    {B : Type u} [CommRing B] [Algebra A B]
    (e : Spec (.of B) ≅ Z)
    (compatible : e.hom ≫ i = Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (transitive : IsGeometricallyTransitive A T G)
    (x y : (pullback (Spec.map (CommRingCat.ofHom (algebraMap A T))) i : Scheme.{u}))
    (same_base : pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A T))) i x =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A T))) i y) :
    ∃ g : G, (affineSchemeBaseChangeAction (T := T) (G := G) i g).asIso.hom x = y := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] T)))
  let q := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T).toRingHom)
  have square : IsPullback q (p ≫ e.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap A T))) i := by
    apply (tensorSpecSquare_isPullback A B T).flip.of_iso
      (Iso.refl _) (Iso.refl _) e (Iso.refl _)
    · simp [q]
    · simp [p]
    · simp
    · exact (Category.comp_id _).trans compatible.symm
  have equivariant (g : G) :
      (specAction (T := B ⊗[A] T) g).asIso.hom ≫ square.isoPullback.hom =
        square.isoPullback.hom ≫ (affineSchemeBaseChangeAction (T := T) i g).asIso.hom := by
    exact isPullback_isoPullback_equivariant square specAction specAction 1 1
      (fun g ↦ (specAction_over_base g).trans (Category.comp_id _).symm)
      (fun _ ↦ (Category.id_comp i).trans (Category.comp_id i).symm)
      tensorSpecSquare_right_equivariant
      (fun g ↦ (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ e.hom) (specAction_over_base (A := B) g)).trans
          (Category.comp_id _).symm)) g
  exact schemeFiberTransitivity_of_iso p (pullback.snd _ _) square.isoPullback e
    square.isoPullback_hom_snd specAction (affineSchemeBaseChangeAction i) equivariant
    (specAction_transitive_on_fibers (geometricTransitivity_baseChange transitive))
    x y same_base

/-- 概要：任意のアフィン基底への実際の底変換は点の推移性を持つ（論文 補題 3.2）。
方針：構造射から座標環の A 代数構造を構成し、isoSpec を使う。
規約：基底の代数表示や推移性を追加仮定に残さない。
使われ方：実際の Čech のアフィン各段への適用。 -/
theorem affineSchemeBaseChange_transitive [IsAffine Z]
    (transitive : IsGeometricallyTransitive A T G)
    (x y : (pullback (Spec.map (CommRingCat.ofHom (algebraMap A T))) i : Scheme.{u}))
    (same_base : pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A T))) i x =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A T))) i y) :
    ∃ g : G, (affineSchemeBaseChangeAction (T := T) (G := G) i g).asIso.hom x = y := by
  let φ : A →+* Γ(Z, ⊤) := (Spec.preimage (Z.isoSpec.inv ≫ i)).hom
  let : Algebra A Γ(Z, ⊤) := φ.toAlgebra
  exact affineSchemeBaseChange_transitive_of_coordinates i Z.isoSpec.symm
    (Spec.map_preimage (Z.isoSpec.inv ≫ i)).symm transitive x y same_base

end SerrePositivity.KST.Descent
