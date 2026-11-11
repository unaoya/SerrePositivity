module
public import SerrePositivity.KST.Spectra.KanSequence

public import SerrePositivity.KST.Spectra.PointedHomotopyClasses
public import SerrePositivity.KST.Spectra.PointedHomotopyExtension
public import SerrePositivity.KST.Spectra.SpectrumHomotopyEquivalences
public import SerrePositivity.KST.Spectra.UnbasedHomotopyIsomorphism

/-!
概要：ホモトピー可換な Kan 列の段の比較を実際の厳密な射へ直す。
方針：源の単射な構造射に沿い、前段を保つ相対ホモトピー充填で次段を修正する。
規約：高次の coherence を入力せず、各段の成分の構造可換式を明示する。
使われ方：BF 1978 §2、HTT A.3.3、Goerss–Jardine I §7。次数移動の模型の比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.KanSequence

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : KanSequence.{u}} (hX : ∀ n, Mono (X.sigma n).right)
  (f : ∀ n, (X.level n).space ⟶ (Y.level n).space)
  (hf : ∀ n, PointedMapping.componentOf (PointedSimplicialSet.circle.{u} ◁ f n ≫ Y.sigma n) =
    PointedMapping.componentOf (X.sigma n ≫ f (n + 1)))

/-- 概要：指定した射と同じ成分を保つ一段の修正データ。
方針：射とその成分の等式を対にする。
規約：次段との厳密な可換性は次段を作る際に保持する。
使われ方：BF 1978 §2。厳密化の逐次構成の状態。 -/
def RectificationStage (n : ℕ) :=
  { g : (X.level n).space ⟶ (Y.level n).space //
    PointedMapping.componentOf g = PointedMapping.componentOf (f n) }

/-- 概要：一段の修正から構造射と厳密に可換な次段を作る。
方針：suspension と合成の成分の整合性を使い、源の単射へホモトピーを延長する。
規約：次段も元の指定した射と同じ成分を保つ。
使われ方：BF 1978 §2、HTT A.3.3。ホモトピー可換な射の厳密化の帰納段。 -/
def rectificationNext (n : ℕ) (s : RectificationStage f n) :
    { t : RectificationStage f (n + 1) //
      X.sigma n ≫ t.val = PointedSimplicialSet.circle.{u} ◁ s.val ≫ Y.sigma n } := by
  letI : Mono (X.sigma n).right := hX n
  have hs := PointedMapping.componentOf_comp_right
    (PointedMapping.componentOf_suspension s.property) (Y.sigma n)
  have h : PointedMapping.componentOf (X.sigma n ≫ f (n + 1)) =
      PointedMapping.componentOf (PointedSimplicialSet.circle.{u} ◁ s.val ≫ Y.sigma n) :=
    (hs.trans (hf n)).symm
  let hex := PointedExtension.exists_adjustment (X.sigma n) (f (n + 1))
    (PointedSimplicialSet.circle.{u} ◁ s.val ≫ Y.sigma n) h
  exact ⟨⟨hex.choose, hex.choose_spec.2.symm⟩, hex.choose_spec.1⟩

/-- 概要：全ての段を構造射に沿って順に修正する。
方針：零段を保ち、各後続段で相対充填を行う。
規約：選択の自然性はここでは要求しない。
使われ方：BF 1978 §2。厳密な射の全成分。 -/
def rectificationStage : (n : ℕ) → RectificationStage f n
  | 0 => ⟨f 0, rfl⟩
  | n + 1 => (rectificationNext hX f hf n (rectificationStage n)).val

/-- 概要：段ごとにホモトピー可換な比較から構成する厳密な Kan 列の射。
方針：逐次的に修正した段と、各帰納段の厳密な可換式を束ねる。
規約：源の構造射の単射性と標的の Kan 性を使う。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。次数移動の実際の比較射。 -/
def rectify : Hom X Y where
  app n := (rectificationStage hX f hf n).val
  comm n := (rectificationNext hX f hf n (rectificationStage hX f hf n)).property.symm

/-- 概要：厳密化後の各段は元の射と同じ点つきホモトピー類。
方針：帰納状態に保持した成分の等式を取り出す。
規約：全ての段で成立する。
使われ方：Goerss–Jardine I §7、BF 1978 §2。厳密化後の π_* の検査。 -/
theorem rectify_component (n : ℕ) :
    PointedMapping.componentOf ((rectify hX f hf).app n) = PointedMapping.componentOf (f n) :=
  (rectificationStage hX f hf n).property

/-- 概要：厳密化は各段の全基点 π_* 同型性を保つ。
方針：成分の等式を実際のホモトピーへ戻し、全基点同型性のホモトピー不変性を使う。
規約：零次数を含む。
使われ方：Goerss–Jardine I §7、BF 1978 §2。実際の比較射の同型性。 -/
theorem rectify_levelwise (hpi : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f n).right) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((rectify hX f hf).app n).right := by
  obtain ⟨H, _⟩ := (PointedMapping.piZero_eq_iff_pointedHomotopy _ _).mp
    (rectify_component hX f hf n)
  exact (kanPiIsomorphism_iff_of_homotopy H).mpr (hpi n)

end

end SerrePositivity.KST.Spectra.KanSequence
