module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyFunctor

/-!
概要：整数次数の π_* 同型と段ごとの π_* 同型の関係。
方針：標準段の誘導写像の全単射性を可換群の同型に束ねる。
規約：coherent nerve 内の同値との比較はここでは主張しない。
使われ方：BF 1978 §2、HA §1.4.2。定理 3.1 と置換の公開界面。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：スペクトルの射が全整数次数でホモトピー群の同型を誘導する条件。
方針：構成済みの誘導準同型の全単射性で定義する。
規約：追加の公理や同型の入力ではなく、射の性質。
使われ方：BF 1978 §2、HA §1.4.2。定理 3.1 の全次数の主張。 -/
def PiIsomorphism {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) : Prop :=
  ∀ j : ℤ, Function.Bijective (homotopyMap f j)

/-- 概要：整数次数の π_* 同型は恒等射を含む。
方針：誘導準同型の恒等法則を使う。
規約：全整数次数。
使われ方：BF 1978 §2。π_* 同型の合成の界面。 -/
theorem PiIsomorphism.id (X : OmegaSpectrum.{u}) : PiIsomorphism (𝟙 X) := by
  intro j
  rw [homotopyMap_id]
  exact Function.bijective_id

/-- 概要：整数次数の π_* 同型は合成で閉じる。
方針：誘導準同型の合成法則と全単射の合成を使う。
規約：通常の厳密なスペクトルの射。
使われ方：BF 1978 §2。置換比較の合成。 -/
theorem PiIsomorphism.comp {X Y Z : OmegaSpectrum.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : PiIsomorphism f) (hg : PiIsomorphism g) : PiIsomorphism (f ≫ g) := by
  intro j
  rw [homotopyMap_comp]
  exact (hg j).comp (hf j)

/-- 概要：全整数次数の π_* 同型から各次数の可換群の同型を得る。
方針：既存の誘導準同型を全単射性で群同型へ束ねる。
規約：順写像は homotopyMap そのもの。
使われ方：BF 1978 §2、HA §1.4.2。定理 3.1 の利用側。 -/
def PiIsomorphism.groupEquiv {X Y : OmegaSpectrum.{u}} {f : X ⟶ Y}
    (hf : PiIsomorphism f) (j : ℤ) : homotopyGroup X j ≃* homotopyGroup Y j :=
  MulEquiv.ofBijective (homotopyMap f j) (hf j)

/-- 概要：各段で全基点の π_* 同型であるスペクトルの射は整数次数の π_* 同型。
方針：標準段での指定基点の自然数次数の全単射性を使う。
規約：零次数も含む全基点の条件を各段に課す。
使われ方：BF 1978 §2、HA §1.4.2。置換の段ごとの検証からの帰結。 -/
theorem piIsomorphism_of_levelwise {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (hf : ∀ k, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app k).right) : PiIsomorphism f := by
  intro j
  have hb := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism (degree j (canonicalLevel j))
    (f.app (canonicalLevel j)).right (hf _) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)).bijective
  have heq : (fun a : homotopyGroup X j ↦ homotopyMap f j a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism (degree j (canonicalLevel j))
        (f.app (canonicalLevel j)).right (hf _) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) := by
    funext a
    rw [homotopyMap_apply]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism_apply _ _ _ _ a).symm
  change Function.Bijective (fun a : homotopyGroup X j ↦ homotopyMap f j a)
  rw [heq]
  exact hb

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
