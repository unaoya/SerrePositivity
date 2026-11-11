module

public import SerrePositivity.KST.Spectra.SequenceHomotopyRectification
public import SerrePositivity.KST.Spectra.CofibrantOmegaSequence
public import SerrePositivity.KST.Spectra.CofibrantSequenceLifting

/-!
概要：Kan Ω 列へのホモトピー可換な比較を BF 対象間の厳密な射にする。
方針：源の単射構造射に沿って厳密化し、標的の cofibrant 置換へ持ち上げる。
規約：標的の置換前の構造射の単射性を要求しない。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。次数移動の実際の比較射。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) (hY : Y.OmegaCondition)
  (f : ∀ n, (X.level n).space ⟶ (Y.level n).space)
  (hf : ∀ n, PointedMapping.componentOf (PointedSimplicialSet.circle.{u} ◁ f n ≫ Y.sigma n) =
    PointedMapping.componentOf (X.sigma n ≫ f (n + 1)))

/-- 概要：Kan Ω 列へのホモトピー可換な段の比較から BF 対象間の厳密な射を構成する。
方針：まず元の Kan 列へ厳密化し、cofibrant 置換の比較射へ持ち上げる。
規約：実際の各段の射と成分での構造可換式を入力とする。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。次数移動の厳密な比較。 -/
def rectifyInto : X ⟶ Y.cofibrantOmegaSpectrum hY := by
  let g := KanSequence.liftHom (X := X.toKanSequence)
    (W := (Y.cofibrantOmegaSpectrum hY).toKanSequence) (Z := Y) X.sigma_mono
      (Y.cofibrantOmegaProjection hY) (fun n => (Y.replacementStage n).projection_rlp)
      (KanSequence.rectify (X := X.toKanSequence) (Y := Y) X.sigma_mono f hf)
  exact { app := g.app, comm := g.comm }

/-- 概要：BF 対象への持ち上げを元の列へ戻すと厳密化した比較と一致する。
方針：持ち上げの厳密な因子分解式を使う。
規約：各段の点つき射の等式。
使われ方：BF 1978 §2。比較射の全基点での検査。 -/
theorem rectifyInto_projection (n : ℕ) :
    (rectifyInto X Y hY f hf).app n ≫ (Y.cofibrantOmegaProjection hY).app n =
      (KanSequence.rectify (X := X.toKanSequence) (Y := Y) X.sigma_mono f hf).app n :=
  KanSequence.liftHom_fac (X := X.toKanSequence)
    (W := (Y.cofibrantOmegaSpectrum hY).toKanSequence) (Z := Y) X.sigma_mono
      (Y.cofibrantOmegaProjection hY) (fun n => (Y.replacementStage n).projection_rlp)
      (KanSequence.rectify (X := X.toKanSequence) (Y := Y) X.sigma_mono f hf) n

/-- 概要：元の段の比較が全基点の同型なら BF 比較射も各段で全基点の同型。
方針：厳密化のホモトピー不変性と標的の cofibrant 比較の同型性を使う。
規約：零次数を含む全ての基点。
使われ方：Goerss–Jardine I §7、BF 1978 §2。実際のスペクトルの比較射の検査。 -/
theorem rectifyInto_levelwise (hpi : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f n).right) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((rectifyInto X Y hY f hf).app n).right := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := ((Y.cofibrantOmegaProjection hY).app n).right) _
    (Y.replacementProjection_piIsomorphism n)
  have h := congrArg Under.Hom.right (rectifyInto_projection X Y hY f hf n)
  change ((rectifyInto X Y hY f hf).app n).right ≫
      ((Y.cofibrantOmegaProjection hY).app n).right =
        ((KanSequence.rectify (X := X.toKanSequence) (Y := Y) X.sigma_mono f hf).app n).right at h
  rw [h]
  exact KanSequence.rectify_levelwise (X := X.toKanSequence) (Y := Y) X.sigma_mono f hf hpi n

/-- 概要：全基点の同型な段の比較から構成した厳密な BF 射は π_* 同型。
方針：各段での同型性を整数次数へ移す。
規約：全整数次数の群の同型性。
使われ方：BF 1978 §2、HA §1.4.2。次数移動の実際のスペクトルの比較。 -/
theorem rectifyInto_piIsomorphism (hpi : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f n).right) :
    PiIsomorphism (rectifyInto X Y hY f hf) :=
  piIsomorphism_of_levelwise _ (rectifyInto_levelwise X Y hY f hf hpi)

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
