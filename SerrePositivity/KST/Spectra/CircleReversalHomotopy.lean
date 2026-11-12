module

public import SerrePositivity.KST.Spectra.CircleMappingComponents
public import SerrePositivity.KST.Spectra.CircleClassMap
public import SerrePositivity.KST.Spectra.PointedPrecompositionNaturality

/-!
概要：円の二重符号反転を恒等射へ戻す区間を、円そのもので一度だけ選ぶ。
方針：指定基本類の像で成分を比較し、同じ源区間を各標的の前合成へ移す。
規約：標的ごとに区間を選ばない。使われ方：自然な二重符号反転の構造入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.CirclePower

/-- 円そのものの二度の符号反転は、指定基本類の像から恒等射と同じ成分を持つ。 -/
lemma reversal_twice_component :
    PointedMapping.componentOf (integerPowerMap.{u} (-1) ≫ integerPowerMap (-1)) =
      PointedMapping.componentOf (𝟙 space.{u}) := by
  apply (componentEquiv space.{u}).injective
  change componentEquiv space (SSet.π₀.mk (PointedMapping.familyVertex _)) =
    componentEquiv space (SSet.π₀.mk (PointedMapping.familyVertex _))
  rw [componentEquiv_familyVertex, componentEquiv_familyVertex,
    evaluateGenerator_integerPower, evaluateGenerator_integerPowerMap]
  simp only [zpow_neg_one, inv_inv, evaluateGenerator, Under.id_right]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_id]
  rfl

/-- 全ての標的への作用に共通に使う、円自身の同じ二重反転区間。 -/
def reversalTwicePath :
    PointedMapping.VerticalPath (PointedObject.toPoint space.{u})
      (integerPowerMap (-1) ≫ integerPowerMap (-1)) (𝟙 space) :=
  PointedMapping.basedPathOfComponent reversal_twice_component

/-- 同じ円区間を移した、一重 loop の二重反転を恒等へ戻す実区間。 -/
def reversalTwicePre (Y : PointedSimplicialSet.{u}) :
    PointedMapping.VerticalPath (PointedObject.toPoint (PointedObject.basedHom space Y))
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (integerPowerMap (-1)) Y ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (integerPowerMap (-1)) Y)
      (𝟙 (PointedObject.basedHom space Y)) := by
  have hs := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp (integerPowerMap.{u} (-1))
    (integerPowerMap (-1)) Y
  have ht : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (𝟙 space.{u}) Y = 𝟙 _ := by
    rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    exact congrArg (fun t => t.app Y) (MonoidalClosed.pre_id space.{u})
  exact (reversalTwicePath.basedPre Y).changeEndpoints hs ht.symm

/-- 端点の表示変更後も、円自身の同じ前合成区間の辺を保持する。 -/
lemma reversalTwicePre_path (Y : PointedSimplicialSet.{u}) :
    (reversalTwicePre Y).path = (reversalTwicePath.basedPre Y).path := rfl

/-- この同じ二重反転区間は、任意の標的射への後合成と区間全体で自然。 -/
lemma reversalTwicePre_natural {Y Z : PointedSimplicialSet.{u}} (v : Y ⟶ Z) :
    (reversalTwicePre Y).path ≫
      (PointedObject.basedHomMap (PointedObject.basedHom space.{u} Y)
        (Y := PointedObject.basedHom space.{u} Y) (Z := PointedObject.basedHom space.{u} Z)
        (PointedObject.basedHomMap space.{u} (Y := Y) (Z := Z) v)).right =
    (reversalTwicePre Z).path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
        (PointedObject.basedHomMap space.{u} (Y := Y) (Z := Z) v)
        (PointedObject.basedHom space.{u} Z)).right := by
  rw [reversalTwicePre_path, reversalTwicePre_path]
  exact reversalTwicePath.basedPre_post_path v

end SerrePositivity.KST.Spectra.CirclePower
