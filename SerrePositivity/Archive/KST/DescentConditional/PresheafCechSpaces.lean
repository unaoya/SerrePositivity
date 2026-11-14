module

public import SerrePositivity.Archive.KST.DescentConditional.CechDescentRetract
public import SerrePositivity.KST.Descent.CechTransferRetract

/-!
# 元の前層の指定増強と実際のホモトピー比較

## 概要
基底上の幾何図式への前層の像を、増強を保持する単体集合の図式へ関手的に送る。

## 方針
前層の指定増強を実際の値域関手で写し、comma 圏の射を自然性から構成する。
前層の transfer retract をこの関手で写して、実際の指定比較の降下を移す。

## 規約
値域関手は明示した引数。π と Tot の交換や、分裂側の降下自体は仮定しない。

## 使われ方
論文 補題 3.2 の有限平坦 transfer の接続。τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u v w t z

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] {V : Type w} [Category.{t} V]
  {K : Type z} [SmallCategory K] {Y : C} (D : K ⥤ Over Y) (U : V ⥤ SSet.{z})

/-- 概要：元の前層から指定増強を保持する空間図式への実際の関手（補題 3.2）。
方針：構造射の反変像と前層射の自然性を値域関手で写す。
規約：基底での値と各段の値を両方保持。使われ方：実際の transfer retract の移送。 -/
def presheafAugmentedCechSpaces : ((Over Y)ᵒᵖ ⥤ V) ⥤ AugmentedCechDiagram Kᵒᵖ where
  obj F :=
    { left := U.obj (F.obj (op (Over.mk (𝟙 Y))))
      right := (D.op ⋙ F) ⋙ U
      hom :=
        { app k := U.map ((presheafDiagramAugmentation D F).app k)
          naturality {i j} f := by
            change 𝟙 _ ≫ U.map _ = U.map _ ≫ U.map _
            rw [Category.id_comp, ← U.map_comp]
            exact congrArg U.map
              ((Category.id_comp _).symm.trans
                ((presheafDiagramAugmentation D F).naturality f)) } }
  map {F G} a :=
    { left := U.map (a.app (op (Over.mk (𝟙 Y))))
      right := Functor.whiskerRight (Functor.whiskerLeft D.op a) U
      w := by
        apply NatTrans.ext
        funext k
        change U.map _ ≫ U.map _ = U.map _ ≫ U.map _
        rw [← U.map_comp, ← U.map_comp]
        exact congrArg U.map
          (a.naturality (overDiagramToBase D k.unop).op).symm }
  map_id F := by
    apply CommaMorphism.ext
    · exact U.map_id _
    · apply NatTrans.ext
      funext k
      exact U.map_id _
  map_comp a b := by
    apply CommaMorphism.ext
    · exact U.map_comp _ _
    · apply NatTrans.ext
      funext k
      exact U.map_comp _ _

variable [ModelCategory SSet.{z}]
  (I J : MorphismProperty SSet.{z}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{z} I J]

/-- 概要：前層の retract は実際の指定降下を元の前層へ戻す（補題 3.2）。
方針：増強を保持する関手で retract を写し、実際の比較の弱同値を移す。
規約：値域関手の加法性は不要。使われ方：有理的に正規化した transfer の適用。 -/
theorem presheafCechSpaceDescent_of_retract {F G : (Over Y)ᵒᵖ ⥤ V}
    (h : Retract F G)
    (hG : HasCechSpaceDescent Kᵒᵖ I J ((presheafAugmentedCechSpaces D U).obj G)) :
    HasCechSpaceDescent Kᵒᵖ I J ((presheafAugmentedCechSpaces D U).obj F) :=
  cechSpaceDescent_of_retract Kᵒᵖ I J (h.map (presheafAugmentedCechSpaces D U)) hG

variable [HasPullbacks C] [Preadditive V] [Linear ℚ V]

/-- 概要：有限平坦 transfer の局所 rank 公式から実際の指定降下を戻す（補題 3.2）。
方針：元の前層と実際の底変換前層の retract を作り、指定増強の関手で写す。
規約：transfer と自然な rank 公式は明示した入力。分裂側の降下は別に証明する。
使われ方：Čech 図式に適用して、底変換後の降下から元の比較の弱同値を得る。 -/
theorem BaseChangeTransfer.cechSpaceDescent {X : C} {f : X ⟶ Y}
    {F : Cᵒᵖ ⥤ V} (tr : BaseChangeTransfer f F)
    (rank : ℕ) (positive : 0 < rank)
    (rank_identity : baseChangePresheafPullback f F ≫ tr.transfer =
      (rank : ℚ) • 𝟙 (overPresheaf (Y := Y) F))
    (hG : HasCechSpaceDescent Kᵒᵖ I J
      ((presheafAugmentedCechSpaces D U).obj (baseChangedPresheaf f F))) :
    HasCechSpaceDescent Kᵒᵖ I J
      ((presheafAugmentedCechSpaces D U).obj (overPresheaf (Y := Y) F)) :=
  presheafCechSpaceDescent_of_retract D U I J
    (BaseChangeTransfer.retract f tr rank positive rank_identity) hG

end SerrePositivity.KST.Descent
