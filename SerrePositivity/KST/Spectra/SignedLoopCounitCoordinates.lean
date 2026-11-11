module

public import SerrePositivity.KST.Spectra.SignedLoopSequence
public import SerrePositivity.KST.Spectra.KanLoopCounitCoordinates

/-!
概要：符号付き loop 列の構造比較の両端を通常の二重円の座標で計算する。
方針：元の構造射の随伴式と Kan 随伴の制限式を厳密に適用する。
規約：二つの座標の等式や区間の収縮を仮定しない。
使われ方：HA §1.4.2。counit 像に残る円交換と符号反転の特定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.KanSequence
variable (Y : KanSequence.{u})

/-- 元の二段構造の随伴。両方の円は通常の円。 -/
def ordinaryDoubleAdjoint (n : ℕ) :
    (Y.level n).space ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (Y.level (n + 2)).space) :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (Y.sigma n) ≫
    (ihom PointedSimplicialSet.circle.{u}).map
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (Y.sigma (n + 1)))

/-- 符号付き構造の counit 座標。交換後の内側に次数 -1 と通常の円への制限が残る。 -/
def signedDoubleAdjoint (n : ℕ) :
    (Y.level n).space ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (Y.level (n + 2)).space) :=
  kanAdjoint Y n ≫
    (ihom CirclePower.space.{u}).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (Y.sigma (n + 1))) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} PointedSimplicialSet.circle.{u}
      (Y.level (n + 2)).space).hom ≫
    (ihom PointedSimplicialSet.circle.{u}).map
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1))
        (Y.level (n + 2)).space ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} (Y.level (n + 2)).space)

/-- 元の二段構造側を通常の円へ制限して随伴を取ると、通常の二重随伴そのもの。 -/
lemma ordinaryDoubleAdjoint_eq (n : ℕ) :
    curry (Y.sigma n ≫ kanAdjoint Y (n + 1) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} (Y.level (n + 2)).space) =
        ordinaryDoubleAdjoint Y n := by
  rw [kanAdjoint_comparison, curry_natural_right]
  rfl

/-- 符号付き構造側の制限と随伴を厳密に展開した式。 -/
lemma signedDoubleAdjoint_eq (n : ℕ) :
    curry ((PointedSimplicialSet.circle.{u} ◁ kanAdjoint Y n ≫
      (signedLoopTail Y).sigma n) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} (Y.level (n + 2)).space) =
        signedDoubleAdjoint Y n := by
  rw [curry_natural_right, curry_natural_left]
  change (kanAdjoint Y n ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ ((signedLoopTail Y).sigma n)) ≫ _ = _
  erw [signedLoopTail_adjoint]
  simp only [signedDoubleAdjoint, Functor.map_comp, Category.assoc]

/-- 随伴を戻しても同じ符号付き構造射の通常円への制限を回収する。 -/
lemma uncurry_signedDoubleAdjoint (n : ℕ) :
    uncurry (signedDoubleAdjoint Y n) =
      (PointedSimplicialSet.circle.{u} ◁ kanAdjoint Y n ≫
        (signedLoopTail Y).sigma n) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} (Y.level (n + 2)).space := by
  rw [← signedDoubleAdjoint_eq, uncurry_curry]

end SerrePositivity.KST.Spectra.KanSequence
