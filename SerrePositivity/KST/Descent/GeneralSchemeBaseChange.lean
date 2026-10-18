module

public import SerrePositivity.KST.Descent.AffineSchemeBaseChange
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# 一般の基底変更での幾何的推移性の帰結

## 概要
元の環論的な幾何的推移性から、任意のスキームへの実際の底変換の点の推移性を導く。

## 方針
共通の基底点のアフィン近傍へ二点を持ち上げ、アフィンの場合の群元を同変な底変換射で戻す。

## 規約
通常の点の推移性の任意の底変換での保存は仮定しない。元の幾何的推移性を使う。

## 使われ方
論文 補題 3.2・3.3 と定理 3.1 の blowup・中心への底変換でも同じ指定作用を使う。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：二段の基底変更の間の指定射（論文 補題 3.2）。
方針：始域側を固定し、基底側の射を pullback.map に入れる。
規約：圏の実際の指定引き戻しを使う。使われ方：アフィン近傍から一般の基底へ戻す。 -/
noncomputable def schemePullbackChange {X Y Z U : Scheme.{u}}
    (f : X ⟶ Y) (i : Z ⟶ Y) (j : U ⟶ Z) : pullback f (j ≫ i) ⟶ pullback f i :=
  pullback.map f (j ≫ i) f i (𝟙 X) j (𝟙 Y) (by simp) (by simp)

/-- 概要：二段の基底変更の指定射も実際の Cartesian 正方形を作る（補題 3.2）。
方針：元の二つの引き戻しの普遍性と右側の貼り合わせの消去を使う。
規約：点の持ち上げに使う実際のスキームの引き戻し。
使われ方：同じアフィン近傍へファイバーの二点を同時に持ち上げる。 -/
theorem schemePullbackChange_isPullback {X Y Z U : Scheme.{u}}
    (f : X ⟶ Y) (i : Z ⟶ Y) (j : U ⟶ Z) :
    IsPullback (schemePullbackChange f i j) (pullback.snd f (j ≫ i)) (pullback.snd f i) j := by
  have hf : schemePullbackChange f i j ≫ pullback.fst f i = pullback.fst f (j ≫ i) := by
    simp [schemePullbackChange, pullback.map]
  have hs : schemePullbackChange f i j ≫ pullback.snd f i =
      pullback.snd f (j ≫ i) ≫ j := pullback.lift_snd _ _ _
  have H : IsPullback (schemePullbackChange f i j ≫ pullback.fst f i)
      (pullback.snd f (j ≫ i)) f (j ≫ i) :=
    Eq.mpr (congrArg (fun a ↦ IsPullback a (pullback.snd f (j ≫ i)) f (j ≫ i)) hf)
      (IsPullback.of_hasPullback f (j ≫ i))
  exact H.of_right hs (IsPullback.of_hasPullback f i)

variable {A T G : Type u} [CommRing A] [CommRing T] [Algebra A T]
  [Group G] [MulSemiringAction G T] [SMulCommClass G A T]
  {Z : Scheme.{u}} (i : Z ⟶ Spec (.of A))

/-- 概要：任意のスキームへの実際の底変換に点のファイバーの推移性がある（補題 3.2・3.3）。
方針：共通の基底点のアフィン近傍へ両点を持ち上げ、同変な指定射でアフィンの場合の群元を戻す。
規約：有限型性・Noether 性・群の有限性は不要。指定作用の構成自体はアフィン性を使わない。
使われ方：blowup 上を含む一般の基底変更への幾何的推移性の供給。 -/
theorem schemeBaseChange_transitive (transitive : IsGeometricallyTransitive A T G)
    (x y : (pullback (Spec.map (CommRingCat.ofHom (algebraMap A T))) i : Scheme.{u}))
    (same_base : pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A T))) i x =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A T))) i y) :
    ∃ g : G, (affineSchemeBaseChangeAction (T := T) (G := G) i g).asIso.hom x = y := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A T))
  let p := pullback.snd f i
  obtain ⟨R, j, _, z, hz⟩ := Z.exists_Spec_apply_eq (p x)
  let q := schemePullbackChange f i j
  let H := schemePullbackChange_isPullback f i j
  obtain ⟨a, hax, haz⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := j) x z hz.symm
  obtain ⟨b, hby, hbz⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := j) y z
    (same_base.symm.trans hz.symm)
  let x' := H.isoPullback.inv a
  let y' := H.isoPullback.inv b
  have hqx : q x' = x :=
    (congrArg (fun k ↦ k a) H.isoPullback_inv_fst).trans hax
  have hqy : q y' = y :=
    (congrArg (fun k ↦ k b) H.isoPullback_inv_fst).trans hby
  have hxz : pullback.snd f (j ≫ i) x' = z :=
    (congrArg (fun k ↦ k a) H.isoPullback_inv_snd).trans haz
  have hyz : pullback.snd f (j ≫ i) y' = z :=
    (congrArg (fun k ↦ k b) H.isoPullback_inv_snd).trans hbz
  obtain ⟨g, hg⟩ := affineSchemeBaseChange_transitive (T := T) (G := G) (j ≫ i) transitive
    x' y' (hxz.trans hyz.symm)
  have heq : (affineSchemeBaseChangeAction (T := T) (G := G) (j ≫ i) g).asIso.hom ≫ q =
      q ≫ (affineSchemeBaseChangeAction (T := T) (G := G) i g).asIso.hom :=
    pullbackAction_map_trivialBase f (j ≫ i) i (specAction (G := G))
      (fun s ↦ specAction_over_base s) j rfl g
  have he := congrArg (fun k ↦ k x') heq
  exact ⟨g, (congrArg (affineSchemeBaseChangeAction (T := T) (G := G) i g).asIso.hom hqx).symm.trans
    (he.symm.trans ((congrArg q hg).trans hqy))⟩

end SerrePositivity.KST.Descent
