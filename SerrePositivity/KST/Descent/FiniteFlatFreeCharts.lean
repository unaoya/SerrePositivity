module

public import SerrePositivity.KST.Descent.AffineFiniteFlatPresentation

/-!
# 一般の有限忠実平坦射の実際の有限自由アフィンチャート

## 概要
基底の各点を、元の射の実際の底変換代数が正の有限基底を持つアフィン開部分で覆う。

## 方針
基底のアフィン近傍へ底変換し、実際のアフィン表示の基本開自明化と Cartesian 正方形を貼る。

## 規約
チャートの自由基底と Cartesian 性は結論として構成する。降下や transfer の存在を含めない。

## 使われ方
論文 補題 3.2 の一般の基底における有限平坦 transfer の局所自明化。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
open scoped TensorProduct

namespace SerrePositivity.KST.Descent

/-- 概要：元のスキーム射の正の有限自由なアフィン底変換チャート（補題 3.2）。
方針：実際の二つの座標環、基底の開包含、元の始域への射、指定 Cartesian 性と基底を保持する。
規約：これは証明で構成するチャートのデータであり、前層の追加の公理ではない。
使われ方：有限基本開被覆の合成と transfer の射影公式への入力。 -/
structure FiniteFreeAffineChart {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- 概要：チャートの基礎環（補題 3.2）。方針：可換環として保持する。
  規約：元の基底のアフィン開部分を表示する。使われ方：局所 transfer の基礎環。 -/
  baseRing : CommRingCat.{u}
  /-- 概要：底変換の始域の座標環（補題 3.2）。方針：実際の可換環として保持する。
  規約：単なる階数だけの表示ではない。使われ方：自由基底の対象。 -/
  sourceRing : CommRingCat.{u}
  /-- 概要：実際の底変換代数構造（補題 3.2）。方針：座標環間の代数構造を保持する。
  規約：以下の射影と基底で同じ構造を使う。使われ方：構造射の Spec。 -/
  algebra : Algebra baseRing sourceRing
  /-- 概要：元の基底へのチャート射（補題 3.2）。方針：実際のスキーム射を保持する。
  規約：開埋め込み性も別に検査する。使われ方：有限開被覆。 -/
  baseMap : Spec baseRing ⟶ Y
  /-- 概要：チャートの始域から元の始域への射（補題 3.2）。方針：実際の射を保持する。
  規約：下の Cartesian 性の第一射影。使われ方：元の被覆の底変換の同定。 -/
  sourceMap : Spec sourceRing ⟶ X
  /-- 概要：基底のチャート射は開埋め込み（補題 3.2）。方針：実際の性質を検査する。
  規約：像が開というだけではない。使われ方：Zariski 被覆への接続。 -/
  openImmersion : IsOpenImmersion baseMap
  /-- 概要：自由基底の有限な本数（補題 3.2）。方針：自然数で指定する。
  規約：正値性を次で保持する。使われ方：有理 transfer の正規化。 -/
  rank : ℕ
  /-- 概要：基底の本数の正値性（補題 3.2）。方針：全射性から証明して供給する。
  規約：rank 零で割らない。使われ方：有理数としての逆数。 -/
  positive : 0 < rank
  /-- 概要：実際の代数の有限自由基底（補題 3.2）。方針：Fin rank を添字にする。
  規約：同じ代数構造を用いる。使われ方：射影公式から局所 rank 公式へ移す。 -/
  basis : letI : Algebra baseRing sourceRing := algebra
    Basis (Fin rank) baseRing sourceRing
  /-- 概要：指定射影による実際の Cartesian 性（補題 3.2）。方針：スキームの普遍性を保持する。
  規約：点集合の Cartesian 性や対象の同型だけに弱めない。使われ方：実際の底変換被覆。 -/
  cartesian : letI : Algebra baseRing sourceRing := algebra
    IsPullback sourceMap (Spec.map (CommRingCat.ofHom (algebraMap baseRing sourceRing)))
      f baseMap

set_option backward.isDefEq.respectTransparency false in
/-- 概要：一般の有限忠実平坦有限表示射は各基底点を有限自由なアフィンチャートで覆う（補題 3.2）。
方針：アフィン近傍での有限自由自明化を選び、二つの実際の Cartesian 正方形を横に貼る。
規約：基底の Noether 性や大域的なアフィン性を要求しない。全射性で正の基底を得る。
使われ方：準コンパクトな基底上の有限自由被覆と、Zariski Čech による局所 transfer。 -/
theorem exists_finiteFreeAffineChart_at_point {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [AlgebraicGeometry.Flat f] [Surjective f] [LocallyOfFinitePresentation f]
    (y : Y) : ∃ (c : FiniteFreeAffineChart f) (z : Spec c.baseRing), c.baseMap z = y := by
  classical
  obtain ⟨R, j, hj, z, hz⟩ := Y.exists_Spec_apply_eq y
  have : IsOpenImmersion j := hj
  let W := pullback f j
  let p : W ⟶ Spec R := pullback.snd f j
  have : IsAffine W := isAffine_of_isAffineHom p
  let B : Type u := Γ(W, ⊤)
  let eX : Spec (.of B) ≅ W := affineTopPresentation W
  let eY : Spec R ≅ Spec R := Iso.refl _
  let φ : R →+* B := affinePresentationMap p eX eY
  let : Algebra R B := φ.toAlgebra
  obtain ⟨s, hs, hbase⟩ := exists_affinePresentation_positive_basis_cover p eX eY
  have havoid : ∃ r ∈ s, r ∉ z.asIdeal := by
    by_contra! h
    apply z.isPrime.ne_top
    apply top_unique
    rw [← hs]
    exact Ideal.span_le.mpr h
  obtain ⟨r, hrs, hrz⟩ := havoid
  obtain ⟨rank, hpos, ⟨b⟩⟩ := hbase r hrs
  let C := Localization.Away r
  let D := C ⊗[R] B
  let g : Spec (.of C) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap R C))
  have hinner : IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        B →ₐ[R] D).toRingHom) ≫ eX.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap C D))) p g := by
    apply (tensorSpecSquare_isPullback R C B).flip.of_iso
      (Iso.refl _) eX (Iso.refl _) eY
    · exact (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (affinePresentationMap_comm p eX eY).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  let c : FiniteFreeAffineChart f := {
    baseRing := .of C
    sourceRing := .of D
    algebra := inferInstance
    baseMap := g ≫ j
    sourceMap := (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      B →ₐ[R] D).toRingHom) ≫ eX.hom) ≫ pullback.fst f j
    openImmersion := inferInstance
    rank := rank
    positive := hpos
    basis := b
    cartesian := hinner.paste_horiz (IsPullback.of_hasPullback f j) }
  have hzmem : z ∈ Set.range (PrimeSpectrum.comap (algebraMap R C)) := by
    rw [PrimeSpectrum.localization_away_comap_range C r]
    exact hrz
  obtain ⟨z', hz'⟩ := hzmem
  refine ⟨c, z', ?_⟩
  exact (congrArg (fun x ↦ j x) hz').trans hz

end SerrePositivity.KST.Descent
