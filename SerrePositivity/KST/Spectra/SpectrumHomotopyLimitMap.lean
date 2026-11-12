module

public import SerrePositivity.KST.Spectra.KanSequenceHomotopyLimitMap
public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitCone
public import SerrePositivity.KST.Spectra.FixedPointSpectra

/-!
概要：段ごとの homotopy end の BF 対象の実際の射への作用。
方針：Kan 列の end の厳密な射を、cofibrant な源から BF 比較へ持ち上げる。
規約：持ち上げの厳密な関手法則を仮定せず、成分ごとの π_* 同型保存を示す。
使われ方：HA §1.4.2、BF 1978 §2、HTT A.3.3。hG・Tot の実際の射への作用。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace KanSequence

variable {I : Type u} [SmallCategory I] {D E : I ⥤ KanSequence.{u}}
  (hD : ∀ i, (D.obj i).OmegaCondition) (hE : ∀ i, (E.obj i).OmegaCondition)

/-- 概要：Kan Ω 列の図式の射から homotopy end の実際の BF 射を構成する。
方針：源の BF 比較と end の列の射の合成を標的の BF 比較へ持ち上げる。
規約：選んだ厳密な持ち上げを固定する。
使われ方：HA §1.4.2、BF 1978 §2、HTT A.3.3。hG・Tot の係数の射への作用。 -/
def homotopyLimitSpectrumMap (τ : D ⟶ E) :
    homotopyLimitSpectrum D hD ⟶ homotopyLimitSpectrum E hE := by
  let f := liftHom (X := (homotopyLimitSpectrum D hD).toKanSequence)
    (W := (homotopyLimitSpectrum E hE).toKanSequence) (Z := homotopyLimit E)
    (homotopyLimitSpectrum D hD).sigma_mono (homotopyLimitProjection E hE)
    (fun n ↦ (replacementStage (homotopyLimit E) n).projection_rlp)
    ((homotopyLimitProjection D hD).comp (homotopyLimitMap τ))
  exact { app := f.app, comm := f.comm }

/-- 概要：BF end の射を置換前へ射影すると Kan end の厳密な射になる。
方針：列の持ち上げの因子分解式を使う。
規約：各段の点つき射の厳密な等式。
使われ方：HA §1.4.2、BF 1978 §2。係数の比較の π_* を検査する。 -/
theorem homotopyLimitSpectrumMap_projection (τ : D ⟶ E) (n : ℕ) :
    (homotopyLimitSpectrumMap hD hE τ).app n ≫ (homotopyLimitProjection E hE).app n =
      (homotopyLimitProjection D hD).app n ≫ (homotopyLimitMap τ).app n :=
  liftHom_fac (X := (homotopyLimitSpectrum D hD).toKanSequence)
    (W := (homotopyLimitSpectrum E hE).toKanSequence) (Z := homotopyLimit E)
    (homotopyLimitSpectrum D hD).sigma_mono (homotopyLimitProjection E hE)
    (fun k ↦ (replacementStage (homotopyLimit E) k).projection_rlp)
    ((homotopyLimitProjection D hD).comp (homotopyLimitMap τ)) n

/-- 概要：図式の各段の全基点 π_* 同型は BF end の各段でも同型を誘導する。
方針：Kan end の保存性と二つの単射置換の比較を使い標的の射影を打ち消す。
規約：零次数を含み全ての基点で述べる。
使われ方：Goerss–Jardine I §7、HA §1.4.2。hG・Tot の係数の置換不変性。 -/
theorem homotopyLimitSpectrumMap_levelwise (τ : D ⟶ E)
    (hτ : ∀ i n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((τ.app i).app n).right) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((homotopyLimitSpectrumMap hD hE τ).app n).right := by
  have hc := (homotopyLimitProjection_levelwise D hD n).comp (homotopyLimitMap_levelwise τ hτ n)
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := ((homotopyLimitProjection E hE).app n).right) _
    (homotopyLimitProjection_levelwise E hE n)
  have h := congrArg Under.Hom.right (homotopyLimitSpectrumMap_projection hD hE τ n)
  change ((homotopyLimitSpectrumMap hD hE τ).app n).right ≫
    ((homotopyLimitProjection E hE).app n).right =
    ((homotopyLimitProjection D hD).app n).right ≫ ((homotopyLimitMap τ).app n).right at h
  rw [h]
  exact hc

/-- 概要：図式の各段の π_* 同型は BF end の全整数次数でも同型。
方針：各段の全基点の比較を整数次数の任意段表示へ移す。
規約：∞ 極限の比較を仮定しない。
使われ方：HA §1.4.2、BF 1978 §2。hG・Tot の π_* 比較。 -/
theorem homotopyLimitSpectrumMap_piIsomorphism (τ : D ⟶ E)
    (hτ : ∀ i n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((τ.app i).app n).right) :
    OmegaSpectrum.PiIsomorphism (homotopyLimitSpectrumMap hD hE τ) :=
  OmegaSpectrum.piIsomorphism_of_levelwise _ (homotopyLimitSpectrumMap_levelwise hD hE τ hτ)

end KanSequence

namespace OmegaSpectrum

/-- 概要：BF 図式の自然変換が homotopy end の実際の BF 射を誘導する。
方針：図式を Kan 列へ忘れて BF end の持ち上げを使う。
規約：両端は既存の homotopyLimit の対象そのもの。
使われ方：HA §1.4.2、BF 1978 §2。hG・Tot の射への作用。 -/
def homotopyLimitMap {I : Type u} [SmallCategory I] {D E : I ⥤ OmegaSpectrum.{u}} (τ : D ⟶ E) :
    homotopyLimit D ⟶ homotopyLimit E :=
  KanSequence.homotopyLimitSpectrumMap (D := D ⋙ forgetToKan) (E := E ⋙ forgetToKan)
    (fun i ↦ (D.obj i).toKanSequence_omega) (fun i ↦ (E.obj i).toKanSequence_omega)
    (Functor.whiskerRight τ forgetToKan)

end OmegaSpectrum

/-- 概要：同変な BF 射は homotopy fixed points 間の実際の BF 射を誘導する。
方針：作用図式の自然変換を homotopy end の比較へ送る。
規約：射を π_* の同型の移送だけで定義しない。
使われ方：HA §1.4.2、BF 1978 §2、HTT A.3.3。hG の射への作用。 -/
def homotopyFixedPointsMap {G : Type u} [Group G] {A B : GroupAction.{u} G} (f : A ⟶ B) :
    homotopyFixedPoints A ⟶ homotopyFixedPoints B :=
  OmegaSpectrum.homotopyLimitMap
    (Functor.whiskerLeft AsSmall.down ((GroupAction.diagramFunctor G).map f))

/-- 概要：余単体 BF 対象の自然変換は homotopy Tot 間の実際の BF 射を誘導する。
方針：AsSmall で宇宙を揃えて図式の end の比較を適用する。
規約：通常の Tot や ∞ 極限との比較は仮定しない。
使われ方：HA §1.4.2、BF 1978 §2。homotopy Tot の射への作用。 -/
def homotopyTotalizationMap {X Y : CosimplicialObject OmegaSpectrum.{u}} (f : X ⟶ Y) :
    homotopyTotalization X ⟶ homotopyTotalization Y :=
  OmegaSpectrum.homotopyLimitMap (Functor.whiskerLeft AsSmall.down f)

end

end SerrePositivity.KST.Spectra
