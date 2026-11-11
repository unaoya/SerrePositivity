module

public import SerrePositivity.KST.Spectra.CotensorPower
public import SerrePositivity.KST.Spectra.LoopIntegerPower
public import SerrePositivity.KST.Spectra.TwistedOmegaSpectrum

/-!
概要：BF cotensor の整数次数射と、符号を変えた BF 模型への実際の比較。
方針：任意段表示で整数冪を計算し、全基点の符号反転を構造射へ後合成する。
規約：一般の整数次数の射に全基点同型性は主張せず、符号反転でのみ使う。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。次数移動の模型の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：cotensor の源の制限が各段で全基点同型なら BF の持ち上げも同型。
方針：二つの cofibrant 比較射と制限射の厳密な可換式を使って打ち消す。
規約：源の射の anodyne 性を仮定しない。
使われ方：BF 1978 §2、HA §1.4.2。loop の符号反転を BF 対象へ移す。 -/
theorem cotensorPre_levelwise_of_pre_piIsomorphism {A B : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (X : OmegaSpectrum.{u})
    (hi : ∀ k, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (X.level k).space).right)
    (k : ℕ) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((cotensorPre i X).app k).right := by
  have hcomp := (cotensorProjection_piIsomorphism B X k).comp (hi k)
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := ((cotensorProjection A X).app k).right) _
    (cotensorProjection_piIsomorphism A X k)
  have h := congrArg Under.Hom.right (cotensorPre_comparison i X k)
  change ((cotensorPre i X).app k).right ≫ ((cotensorProjection A X).app k).right =
    ((cotensorProjection B X).app k).right ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (X.level k).space).right at h
  rw [h]
  exact hcomp

/-- 概要：円の整数次数射は BF cotensor の全整数次数群に整数冪で作用する。
方針：必ず正次数となる段で、通常の loop の群の整数冪の式を使う。
規約：z と j は任意の整数。
使われ方：BF 1978 §2、HA §1.4.2。スペクトル上の実際の符号反転の作用。 -/
theorem cotensorPre_integer_homotopyMap (X : OmegaSpectrum.{u}) (z j : ℤ)
    (a : homotopyGroup (cotensor CirclePower.space.{u} X) j) :
    homotopyMap (cotensorPre (CirclePower.integerPowerMap z) X) j a = a ^ z := by
  apply (cotensorStageEquiv CirclePower.space X j (boundaryStage j) (boundaryIndex j)
    (boundaryStage_admissible j) (boundaryStage_degree j)).injective
  rw [cotensorStageEquiv_pre, map_zpow]
  exact LoopMappingClasses.groupMap_pre_integer _ z _ _

/-- 概要：円の符号反転の BF cotensor 上の射は各段で全基点の π_* 同型。
方針：実際の loop の符号反転の同型性を BF 比較射に沿って移す。
規約：零次数も含む。
使われ方：Goerss–Jardine I §7、BF 1978 §2。構造射の符号変更の Ω 条件。 -/
theorem cotensorPre_neg_one_levelwise (X : OmegaSpectrum.{u}) (k : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((cotensorPre (CirclePower.integerPowerMap (-1)) X).app k).right :=
  cotensorPre_levelwise_of_pre_piIsomorphism _ X
    (fun k => LoopMappingClasses.pre_neg_one_piIsomorphism (X.level k).space) k

/-- 概要：loop cotensor の構造射の後で符号反転を施した BF 模型。
方針：符号を変えた Ω 列を cofibrant に置換する。
規約：各段の全基点の π_* 同型性を使い Ω 条件を保存する。
使われ方：BF 1978 §2、HTT A.3.3。次数移動の符号を調整した実際の対象。 -/
def negatedCotensor (X : OmegaSpectrum.{u}) : OmegaSpectrum.{u} :=
  twisted (cotensor CirclePower.space.{u} X)
    (sequenceHom (cotensorPre (CirclePower.integerPowerMap (-1)) X))
    (cotensorPre_neg_one_levelwise X)

/-- 概要：loop cotensor から構造射の符号を変えた BF 模型への実際の厳密な射。
方針：各段の反復による比較を cofibrant 置換へ持ち上げる。
規約：射の向きを群の同型から推論せず、充填で構成する。
使われ方：BF 1978 §2、HA §1.4.2。次数移動の符号の実際の比較。 -/
def negatedCotensorComparison (X : OmegaSpectrum.{u}) :
    cotensor CirclePower.space.{u} X ⟶ negatedCotensor X :=
  twistComparison _ _ (cotensorPre_neg_one_levelwise X)

/-- 概要：構造射の符号を変える cotensor の比較は全整数次数で π_* 同型。
方針：各段での全基点の同型性を整数次数へ移す。
規約：Sp の ∞ 圏の同値との比較は主張しない。
使われ方：BF 1978 §2、HA §1.4.2。符号を変えた loop 模型の群の表示。 -/
theorem negatedCotensorComparison_piIsomorphism (X : OmegaSpectrum.{u}) :
    PiIsomorphism (negatedCotensorComparison X) :=
  twistComparison_piIsomorphism _ _ (cotensorPre_neg_one_levelwise X)

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
