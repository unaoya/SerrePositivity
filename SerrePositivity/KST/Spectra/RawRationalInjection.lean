module

public import SerrePositivity.KST.Spectra.RawRationalSpectrum
public import SerrePositivity.KST.Spectra.CotensorPost
public import SerrePositivity.KST.Spectra.PointedComponentCancellation

/-!
概要：既存の telescope の零段の注入射と関手的な Kan 図式の比較。
方針：単射置換の射影後で余極限の注入射を計算する。
規約：スペクトル間の射は実際の厳密な BF 射を使う。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。有理化の単位の自然性。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：関手的な有理 telescope の BF 比較射の各段。
方針：Kan 列の余極限の単射置換の標準射影を取り出す。
規約：各段で全単射 RLP を持つ。
使われ方：BF 1978 §2、HTT A.3.3。比較射の厳密な計算の共通の標的。 -/
abbrev rawRationalLevelProjection (X : OmegaSpectrum.{u}) (n : ℕ) :=
  KanSequence.filteredLevelComparison (rawRationalDiagram X) (rawRationalDiagram_omega X) n

/-- 概要：既存の有理 telescope の比較は段の余極限比較射と整合する。
方針：Kan 図式の自然変換の持ち上げの因子分解式を使う。
規約：点つき射の厳密な等式。
使われ方：BF 1978 §2。零段の注入射の比較。 -/
theorem rationalLoopProjection_comparison (X : OmegaSpectrum.{u}) (n : ℕ) :
    (rationalLoopProjection X).app n ≫ rawRationalLevelProjection X n =
      filteredLevelComparison (rationalDiagram X) n ≫
        colimMap (KanSequence.levelTransformation (rationalDiagramProjection X) n) :=
  KanSequence.filteredSpectrumMap_comparison
    (D := rationalDiagram X ⋙ forgetToKan) (E := rawRationalDiagram X)
    (fun a ↦ ((rationalDiagram X).obj a).toKanSequence_omega)
    (rawRationalDiagram_omega X) (rationalDiagramProjection X) n

/-- 概要：既存の零段注入を二つの比較で戻すと内部 Hom の余極限への標準射。
方針：BF 注入射の比較式と自然変換の余極限の成分式を使う。
規約：零段は AsSmall.up.obj 0。
使われ方：BF 1978 §2、HA §1.4.2。有理化の単位の自然性の計算。 -/
theorem rationalLoopInjection_projection (X : OmegaSpectrum.{u}) (n : ℕ) :
    (filteredSpectrumInjection (rationalDiagram X) (AsSmall.up.obj 0)).app n ≫
      (rationalLoopProjection X).app n ≫ rawRationalLevelProjection X n =
    (cotensorProjection CirclePower.space.{u} X).app n ≫
      colimit.ι (KanSequence.levelDiagram (rawRationalDiagram X) n) (AsSmall.up.obj 0) := by
  rw [rationalLoopProjection_comparison, ← Category.assoc,
    filteredSpectrumInjection_comparison]
  exact colimit.ι_map (KanSequence.levelTransformation (rationalDiagramProjection X) n)
    (AsSmall.up.obj 0)

/-- 概要：内部 Hom の telescope の射は段の余極限の誘導射へ射影される。
方針：自然変換から BF 比較を作る際の因子分解式を取り出す。
規約：点つき射の厳密な等式。
使われ方：BF 1978 §2、HTT A.3.3。単位の自然性の標的側の計算。 -/
theorem rawRationalLoopMap_comparison {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    (rawRationalLoopMap f).app n ≫ rawRationalLevelProjection Y n =
      rawRationalLevelProjection X n ≫
        colimMap (KanSequence.levelTransformation (rawRationalDiagramMap f) n) :=
  KanSequence.filteredSpectrumMap_comparison
    (D := rawRationalDiagram X) (E := rawRationalDiagram Y)
    (rawRationalDiagram_omega X) (rawRationalDiagram_omega Y) (rawRationalDiagramMap f) n

/-- 概要：零段から関手的な telescope への比較は元の射に対して各段の成分で自然。
方針：標的の全単射 RLP 射影で打ち消し、余極限の注入射の自然性を使う。
規約：左辺と右辺の全ての射は実際の BF 射。
使われ方：BF 1978 §2、HA §1.4.2。有理化の単位の自然性の中段。 -/
theorem rationalLoopInjection_natural_component {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    PointedMapping.componentOf
      ((filteredSpectrumInjection (rationalDiagram X) (AsSmall.up.obj 0)).app n ≫
        (rationalLoopProjection X).app n ≫ (rawRationalLoopMap f).app n) =
    PointedMapping.componentOf
      ((cotensorPost CirclePower.space.{u} f).app n ≫
        (filteredSpectrumInjection (rationalDiagram Y) (AsSmall.up.obj 0)).app n ≫
          (rationalLoopProjection Y).app n) := by
  apply PointedMapping.componentOf_eq_of_comp_eq_rlp (rawRationalLevelProjection Y n)
    (KanSequence.replacementStage (KanSequence.filteredKanSequence (rawRationalDiagram Y)) n).projection_rlp
  let iX := (filteredSpectrumInjection (rationalDiagram X) (AsSmall.up.obj 0)).app n
  let iY := (filteredSpectrumInjection (rationalDiagram Y) (AsSmall.up.obj 0)).app n
  let pX := (rationalLoopProjection X).app n
  let pY := (rationalLoopProjection Y).app n
  let qX := rawRationalLevelProjection X n
  let qY := rawRationalLevelProjection Y n
  let c := colimMap (KanSequence.levelTransformation (rawRationalDiagramMap f) n)
  let jX := colimit.ι (KanSequence.levelDiagram (rawRationalDiagram X) n) (AsSmall.up.obj 0)
  let jY := colimit.ι (KanSequence.levelDiagram (rawRationalDiagram Y) n) (AsSmall.up.obj 0)
  let aX := (cotensorProjection CirclePower.space.{u} X).app n
  let aY := (cotensorProjection CirclePower.space.{u} Y).app n
  let t := (cotensorPost CirclePower.space.{u} f).app n
  let b := PointedObject.basedHomMap CirclePower.space.{u} (f.app n)
  have hc : (rawRationalLoopMap f).app n ≫ qY = qX ≫ c :=
    rawRationalLoopMap_comparison f n
  have hiX : iX ≫ pX ≫ qX = aX ≫ jX := rationalLoopInjection_projection X n
  have hiY : iY ≫ pY ≫ qY = aY ≫ jY := rationalLoopInjection_projection Y n
  have hj : jX ≫ c = b ≫ jY :=
    KanSequence.levelTransformation_colimit_ι (rawRationalDiagramMap f) n (AsSmall.up.obj 0)
  have ht : t ≫ aY = aX ≫ b := cotensorPost_comparison CirclePower.space.{u} f n
  change (iX ≫ pX ≫ (rawRationalLoopMap f).app n) ≫ qY = (t ≫ iY ≫ pY) ≫ qY
  calc
    _ = (iX ≫ pX ≫ qX) ≫ c := by simp only [Category.assoc, hc]
    _ = (aX ≫ jX) ≫ c := congrArg (fun z ↦ z ≫ c) hiX
    _ = t ≫ (aY ≫ jY) := by rw [Category.assoc, hj, ← Category.assoc, ← ht, Category.assoc]
    _ = _ := by rw [← hiY]; simp only [Category.assoc]

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
