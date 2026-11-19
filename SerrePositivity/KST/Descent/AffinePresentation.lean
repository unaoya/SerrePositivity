module

public import SerrePositivity.KST.Descent.AffineTensorChartModel

/-!
# 元のアフィンスキームの全切断環による実際の表示

## 概要
全体のアフィン開集合の fromSpec を同型とし、元の有限射の環準同型と有限性を得る。

## 方針
Spec の充満忠実性を用い、元のスキーム射を両端の実際の同型で表示する。

## 規約
元の環と Spec の全切断環を定義上同じものとして扱わない。

## 使われ方
論文 補題 3.3、公理 (6) の標準 blowup チャートの係数写像との実際の整合性。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open SerrePositivity.KST.SchemeLemmas

namespace SerrePositivity.KST.Descent

/-- 概要：アフィンスキームの全体の fromSpec は実際の同型（論文 補題 3.3）。
方針：全体のアフィン開集合の fromSpec の像が全体であることを使う。
規約：hom は標準チャート公式に現れる fromSpec そのもの。
使われ方：全切断環のチャート係数と元のスキームを同じ可換図式で扱う。 -/
noncomputable def affineTopPresentation (Y : Scheme.{u}) [IsAffine Y] :
    Spec Γ(Y, ⊤) ≅ Y := by
  have : IsIso (isAffineOpen_top Y).fromSpec :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ (isAffineOpen_top Y).opensRange_fromSpec
  exact asIso (isAffineOpen_top Y).fromSpec

/-- 概要：全体のアフィン表示は同じ全切断の基本開を保つ（論文 補題 3.3）。
方針：fromSpec の基本開の逆像の既存公式を使う。
規約：境界元は Γ(Y,⊤) の実際の元。
使われ方：生成点付近の自由化で選んだ境界を元のスキームへ戻す。 -/
theorem affineTopPresentation_preimage_basicOpen (Y : Scheme.{u}) [IsAffine Y]
    (r : Γ(Y, ⊤)) : (affineTopPresentation Y).hom ⁻¹ᵁ Y.basicOpen r = PrimeSpectrum.basicOpen r :=
  (isAffineOpen_top Y).fromSpec_preimage_basicOpen r

/-- 概要：整なアフィン基底の非零全切断は非空な基本開を定める（論文 補題 3.3）。
方針：全切断環の零素イデアルの点を実際のアフィン表示で元のスキームへ送る。
規約：境界元は同じ全切断環の元。
使われ方：境界を避ける平坦化中心が真閉部分であることの検証。 -/
theorem affine_basicOpen_nonempty_of_ne_zero (Y : Scheme.{u}) [IsAffine Y] [IsIntegral Y]
    (r : Γ(Y, ⊤)) (hr : r ≠ 0) : (Y.basicOpen r).carrier.Nonempty := by
  let x : Spec Γ(Y, ⊤) := (⊥ : PrimeSpectrum Γ(Y, ⊤))
  have hx : x ∈ (PrimeSpectrum.basicOpen r).carrier := by
    change r ∉ (⊥ : Ideal Γ(Y, ⊤))
    simpa only [Ideal.mem_bot] using hr
  refine ⟨(affineTopPresentation Y).hom x, ?_⟩
  exact Eq.mpr (congrArg (fun W : (Spec Γ(Y, ⊤)).Opens ↦ x ∈ W)
    (affineTopPresentation_preimage_basicOpen Y r)) hx

/-- 概要：非零境界基本開を避ける中心の支持は真閉部分（論文 補題 3.3）。
方針：非空な境界基本開の点が支持の補集合に入ることを使う。
規約：中心の冪零構造や厚みに依存しない支持の主張。
使われ方：平坦化の中心上の次元帰納への接続。 -/
theorem center_support_ne_top_of_nonzero_boundary (Y : Scheme.{u}) [IsAffine Y] [IsIntegral Y]
    (J : Y.IdealSheafData) (r : Γ(Y, ⊤)) (hr : r ≠ 0)
    (hadm : Y.basicOpen r ≤ _root_.SerrePositivity.AlgebraicGeometry.centerComplement J) : J.support ≠ ⊤ := by
  obtain ⟨y, hy⟩ := affine_basicOpen_nonempty_of_ne_zero Y r hr
  intro htop
  have hc := hadm hy
  change y ∉ J.support at hc
  apply hc
  rw [htop]
  trivial

variable {R B : Type u} [CommRing R] [CommRing B] {X Y : Scheme.{u}}
  (f : X ⟶ Y) (eX : Spec (.of B) ≅ X) (eY : Spec (.of R) ≅ Y)

/-- 概要：実際のアフィン表示で元の射を表す環準同型（論文 補題 3.3）。
方針：両端の同型を合成した実際の射の Spec による逆像を取る。
規約：この写像により R 代数構造を定めて加群の有限性・平坦性を扱う。
使われ方：元の有限射の有限加群の平坦化への入力。 -/
noncomputable def affinePresentationMap : R →+* B :=
  (Spec.preimage (eX.hom ≫ f ≫ eY.inv)).hom

/-- 概要：表示した環準同型の Spec は元の実際の表示射に一致（論文 補題 3.3）。
方針：Spec の充満忠実性の map-preimage の等式を使う。
規約：両端の標準同型の hom・inv を保持する。
使われ方：有限性とチャートの可換式の移送。 -/
theorem affinePresentationMap_spec :
    Spec.map (CommRingCat.ofHom (affinePresentationMap f eX eY)) = eX.hom ≫ f ≫ eY.inv :=
  Spec.map_preimage _

/-- 概要：元の射と環準同型の表示の可換性（論文 補題 3.3）。
方針：Spec による表示射の等式に基底の同型の hom を合成する。
規約：元の f を残した可換式。
使われ方：同型を保つテンソル積モデルの hf を供給する。 -/
theorem affinePresentationMap_comm :
    eX.hom ≫ f = Spec.map (CommRingCat.ofHom (affinePresentationMap f eX eY)) ≫ eY.hom := by
  have h : (eX.hom ≫ f ≫ eY.inv) ≫ eY.hom = eX.hom ≫ f := by simp
  exact ((congrArg (· ≫ eY.hom) (affinePresentationMap_spec f eX eY)).trans h).symm

/-- 概要：元のスキーム射が有限なら実際の表示環準同型も有限（論文 補題 3.3）。
方針：同型の合成による有限性と Spec の有限射判定を使う。
規約：表示された写像による代数構造についての有限性。
使われ方：Noether 整域上の有限加群の平坦化の有限性を実際に供給する。 -/
theorem affinePresentationMap_finite [IsFinite f] : (affinePresentationMap f eX eY).Finite := by
  have hi : IsFinite (Spec.map (CommRingCat.ofHom (affinePresentationMap f eX eY))) := by
    rw [affinePresentationMap_spec]
    infer_instance
  exact (IsFinite.SpecMap_iff _).mp hi

/-- 概要：有限射の実際の表示に関する基礎環上の加群有限性（論文 補題 3.3）。
方針：有限な環準同型の定義をその実際の代数構造で使う。
規約：代数構造を明示的に選び、別の構造に無証明で交換しない。
使われ方：生成点付近の自由化とチャート平坦化中心の存在定理の入力。 -/
theorem affinePresentationMap_moduleFinite [IsFinite f] :
    letI : Algebra R B := (affinePresentationMap f eX eY).toAlgebra
    Module.Finite R B :=
  affinePresentationMap_finite f eX eY

end SerrePositivity.KST.Descent
