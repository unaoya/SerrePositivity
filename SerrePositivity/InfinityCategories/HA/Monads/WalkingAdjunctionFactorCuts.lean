module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionCutChains

/-!
概要：実際の全水平分解から、比較可能な切れ目の追跡データを構成する。
方針：検証済みの順序和と端点共有の全射の表示を、切れ目の回収へ移す。
規約：可換条件を仮定せず元の合成から証明する。
使われ方：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の分解の一意性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：minusに入る全ての実射の区間表示は最大元を保つ。
方針：最大元保存のHomと実区間表示を場合分けする。
規約：実際の左因子の条件。使われ方：Riehl–Verity Proposition 3.1.10 の共有点。 -/
lemma walkingAdjunctionIncomingMap_last {X : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X .minus} (f : A ⟶ B) :
    walkingAdjunctionIncomingMap f (Fin.last (walkingAdjunctionIncomingDim X A)) =
      Fin.last (walkingAdjunctionIncomingDim X B) := by
  cases X
  · exact f.property
  · exact ordinalIntervalMap_last (augmentedOrderHom f.unop)

/-- 概要：plus経由の実水平分解の切れ目の全追跡データ。
方針：左因子の点の個数を切れ目とし、順序和の全射の表示から可換条件を証明する。
規約：全頂点と全射を保つ。使われ方：Riehl–Verity Proposition 3.1.10。 -/
def walkingAdjunctionPlusFactorCut {n : ℕ} (X Y : WalkingAdjunctionPoint)
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X .plus)
    (G : Fin (n + 1) ⥤ walkingAdjunctionHom .plus Y) :
    WalkingAdjunctionPlusCut (F.prod' G ⋙ walkingAdjunctionHorizontal X .plus Y) where
  value i := ⟨walkingAdjunctionOrdinalCard X .plus (F.obj i), by
    have h := walkingAdjunctionOrdinalCard_comp_plus X Y (F.obj i) (G.obj i)
    change walkingAdjunctionOrdinalCard X .plus (F.obj i) <
      walkingAdjunctionOrdinalCard X Y
        ((walkingAdjunctionHorizontal X .plus Y).obj (F.obj i, G.obj i)) + 1
    omega⟩
  naturality {i j} h := by
    exact ordinalCut_of_append_profile
      (walkingAdjunctionOrdinalCard_comp_plus X Y (F.obj i) (G.obj i))
      (walkingAdjunctionOrdinalCard_comp_plus X Y (F.obj j) (G.obj j))
      _ (walkingAdjunctionOrderHom (F.map (homOfLE h)))
      (walkingAdjunctionOrderHom (G.map (homOfLE h)))
      (walkingAdjunctionOrderHom_comp_plus X Y (F.map (homOfLE h)) (G.map (homOfLE h)))
      _ _ rfl rfl

/-- 概要：minus経由の実水平分解の共有点の全追跡データ。
方針：左因子の区間の次元を共有点とし、端点共有の全射の表示から可換条件を証明する。
規約：共有点の保存を仮定に追加しない。使われ方：Riehl–Verity Proposition 3.1.10。 -/
def walkingAdjunctionMinusFactorCut {n : ℕ} (X Y : WalkingAdjunctionPoint)
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X .minus)
    (G : Fin (n + 1) ⥤ walkingAdjunctionHom .minus Y) :
    WalkingAdjunctionMinusCut (F.prod' G ⋙ walkingAdjunctionHorizontal X .minus Y) where
  value i := ⟨walkingAdjunctionIncomingDim X (F.obj i), by
    have h := walkingAdjunctionOrdinalCard_comp_minus X Y (F.obj i) (G.obj i)
    change walkingAdjunctionIncomingDim X (F.obj i) <
      walkingAdjunctionOrdinalCard X Y
        ((walkingAdjunctionHorizontal X .minus Y).obj (F.obj i, G.obj i))
    omega⟩
  naturality {i j} h := by
    exact ordinalCut_of_glue_profile
      (walkingAdjunctionOrdinalCard_comp_minus X Y (F.obj i) (G.obj i))
      (walkingAdjunctionOrdinalCard_comp_minus X Y (F.obj j) (G.obj j))
      _ (walkingAdjunctionIncomingMap (F.map (homOfLE h)))
      (walkingAdjunctionOutgoingMap (G.map (homOfLE h)))
      (walkingAdjunctionIncomingMap_last (F.map (homOfLE h)))
      (walkingAdjunctionOrderHom_comp_minus X Y (F.map (homOfLE h)) (G.map (homOfLE h)))
      _ _ rfl rfl

end SerrePositivity.InfinityCategories.HA.Monads
