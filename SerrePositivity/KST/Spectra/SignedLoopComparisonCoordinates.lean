module

public import SerrePositivity.KST.Spectra.SignedLoopComparison
public import SerrePositivity.KST.Spectra.PointedTransposeRestrictions

/-!
概要：符号付き loop 比較の段成分を、元の BF 射影と円の反復反転で厳密に表示する。
方針：twistMap の反復を源の前合成へ移し、通常の円への制限も同じ源射へ合成する。
規約：二回の反転が厳密な恒等射とは仮定しない。
使われ方：HA §1.4.2。元の円評価との全パラメータ比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra
namespace CirclePower

/-- Kan 円の実際の反転射の反復。成分の次数で射そのものを置き換えない。 -/
def reversalIterate : ℕ → (space.{u} ⟶ space.{u})
  | 0 => 𝟙 _
  | n + 1 => integerPowerMap.{u} (-1) ≫ reversalIterate n

/-- n 段の符号補正を含む、通常の円から Kan 円への実際の評価パラメータ。 -/
def signedEvaluationParameter (n : ℕ) : PointedSimplicialSet.circle.{u} ⟶ space.{u} :=
  unit.{u} ≫ reversalIterate n

end CirclePower
namespace KanSequence

/-- twist の反復の各段は、Kan 円の同じ反転の反復による前合成そのもの。 -/
lemma iterateHom_tail_mappingPre_app (Y : KanSequence.{u}) (m n : ℕ) :
    (iterateHom (tailHom (mappingPre (CirclePower.integerPowerMap.{u} (-1)) Y)) m).app n =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.reversalIterate m) (Y.level (n + 1)).space := by
  induction m with
  | zero =>
    simp only [iterateHom, CirclePower.reversalIterate,
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, MonoidalClosed.pre_id]
    rfl
  | succ m ih =>
    change (iterateHom (tailHom (mappingPre (CirclePower.integerPowerMap.{u} (-1)) Y)) m).app n ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) (Y.level (n + 1)).space = _
    rw [ih, CirclePower.reversalIterate, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp]

end KanSequence
namespace OmegaSpectrum

/-- 元の符号付き raw 比較の段座標。反転の回数は段添字そのもの。 -/
lemma signedLoopRawComparison_app (X : OmegaSpectrum.{u}) (n : ℕ) :
    (signedLoopRawComparison X).app n =
      (cotensorProjection CirclePower.space.{u} X).app (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.reversalIterate n) (X.level (n + 1)).space := by
  change (cotensorProjection CirclePower.space.{u} X).app (n + 1) ≫
    (KanSequence.iterateHom
      (KanSequence.tailHom (KanSequence.mappingPre (CirclePower.integerPowerMap.{u} (-1))
        X.toKanSequence)) n).app n = _
  rw [KanSequence.iterateHom_tail_mappingPre_app]
  rfl

/-- 元の比較の通常円への制限は、同じ BF 射影を補正済みパラメータへ制限したもの。 -/
lemma signedLoopRawComparison_restriction (X : OmegaSpectrum.{u}) (n : ℕ) :
    (signedLoopRawComparison X).app n ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} (X.level (n + 1)).space =
      (cotensorProjection CirclePower.space.{u} X).app (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.signedEvaluationParameter n)
          (X.level (n + 1)).space := by
  rw [signedLoopRawComparison_app, Category.assoc, CirclePower.signedEvaluationParameter,
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp]

/-- BF 持ち上げ後の同じ比較射でも、射影・通常円制限の座標は変わらない。 -/
lemma signedLoopComparison_restriction (X : OmegaSpectrum.{u}) (n : ℕ) :
    ((signedLoopComparison X).app n ≫ (signedLoopProjection X).app n) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} (X.level (n + 1)).space =
      (cotensorProjection CirclePower.space.{u} X).app (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.signedEvaluationParameter n)
          (X.level (n + 1)).space := by
  rw [signedLoopComparison_projection, signedLoopRawComparison_restriction]

end OmegaSpectrum
end SerrePositivity.KST.Spectra
