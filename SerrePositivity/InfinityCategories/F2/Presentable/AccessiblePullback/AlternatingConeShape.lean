module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.ComponentConeShape
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.ThinNerveMapExt
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.ClosedPrefixGluing

/-!
概要：現在の一頂点追加で、全交互形状と成分形状の比較を厳密に一致させる。
方針：既存の順序余錐同型の両境界を比較し、thin nerve への全射の等式を得る。
規約：高次整合の比較は順序形状の等式として証明する。
使われ方：実際の相対一段因子化を次の閉前置段へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：現在成分の一頂点追加と全交互形状の一頂点追加は厳密に可換。
方針：左境界と右境界の元の包含を照合して thin nerve の全射を比較する。
規約：元の全形状写像の等式を結論する。
使われ方：追加した現在成分の全図式の一致。 -/
lemma alternatingConeShape_component (κ : Cardinal.{u}) (a : κ.ord.ToType) (c : Fin 2) :
    joinMap (nerveMap (alternatingLowerSection κ (toLex (a, c)) c)) (𝟙 Δ[0]) ≫
        (F1B.posetLowerJoinIso (toLex (a, c))).hom =
      (componentConeIso κ a c).hom ≫
        nerveMap (alternatingClosedSection κ (toLex (a, c)) c) := by
  apply join_hom_into_thinNerve_ext
  · calc
      _ = nerveMap (alternatingLowerSection κ (toLex (a, c)) c) ≫
          nerveMap (strictPrefixToClosed (toLex (a, c))) := by
        rw [← Category.assoc, joinInl_joinMap, Category.assoc, F1B.posetLowerJoinIso_inl]
        rfl
      _ = nerveMap (alternatingComponentLowerToClosed κ (toLex (a, c)) c) ≫
          nerveMap (alternatingClosedSection κ (toLex (a, c)) c) := rfl
      _ = _ := by rw [← Category.assoc, componentConeIso_inl]
  · calc
      _ = nervePoint (⟨toLex (a, c), le_rfl⟩ : {b : AlternatingIndex κ // b ≤ toLex (a, c)}) := by
        rw [← Category.assoc, joinInr_joinMap, Category.id_comp, F1B.posetLowerJoinIso_inr]
      _ = _ := by rw [← Category.assoc, componentConeIso_inr]; rfl

/-- 概要：現在とは異なる成分の閉前置形状には新しい頂点が加わらない。
方針：同じ交互位置の等号なら色が一致することを使う。
規約：元の色と元の順序段を保持する。
使われ方：追加しない成分の全図式をそのまま保持する形状同定。 -/
lemma otherComponent_lt_iff_le (κ : Cardinal.{u}) (a b : κ.ord.ToType)
    (c d : Fin 2) (hd : d ≠ c) :
    toLex (b, d) < toLex (a, c) ↔ toLex (b, d) ≤ toLex (a, c) := by
  constructor
  · exact le_of_lt
  · intro h
    rcases h.lt_or_eq with h | h
    · exact h
    · exact (hd (congrArg (fun x : AlternatingIndex κ ↦ (ofLex x).2) h)).elim

/-- 概要：追加しない成分の厳密前置形状と閉前置形状は元の値を保って同型。
方針：色が異なると二つの上界条件が同値であることを使う。
規約：元の順序形状の厳密な同型。
使われ方：元の他成分表示添字を次の全段へ戻す。 -/
def otherComponentIso (κ : Cardinal.{u}) (a : κ.ord.ToType) (c d : Fin 2) (hd : d ≠ c) :
    nerve (AlternatingComponentLower κ (toLex (a, c)) d) ≅
      nerve (AlternatingComponentClosed κ (toLex (a, c)) d) :=
  nerveSubtypeIso _ _ (fun b ↦ otherComponent_lt_iff_le κ a b c d hd)

/-- 概要：他成分の形状同型の順射は元の成分包含そのもの。
方針：部分型の同じ値を送る定義を読む。
規約：全単体上の等式。
使われ方：他成分表示を変えない前置制限。 -/
lemma otherComponentIso_hom (κ : Cardinal.{u}) (a : κ.ord.ToType) (c d : Fin 2) (hd : d ≠ c) :
    (otherComponentIso κ a c d hd).hom =
      nerveMap (alternatingComponentLowerToClosed κ (toLex (a, c)) d) := rfl

/-- 概要：元の表示添字の延長余錐を現在成分の閉前置図式に移す。
方針：同じ成分の余錐形状同型の逆で前合成する。
規約：元の選んだ延長余錐を変更しない。
使われ方：次の閉前置段の現在成分表示添字。 -/
def extendedComponentIndex (κ : Cardinal.{u}) (a : κ.ord.ToType) (c : Fin 2)
    {I : SSet.{u}} {F : nerve (AlternatingComponentLower κ (toLex (a, c)) c) ⟶ I}
    (j : JoinCocone F) : nerve (AlternatingComponentClosed κ (toLex (a, c)) c) ⟶ I :=
  (componentConeIso κ a c).inv ≫ j.val

/-- 概要：追加後の現在成分表示は元の全前置表示を厳密に保持する。
方針：余錐形状同型の左境界と延長余錐の固定条件を使う。
規約：元の全単体上の制限の等式。
使われ方：全過去段を保持する閉前置段の再帰条件。 -/
lemma extendedComponentIndex_old (κ : Cardinal.{u}) (a : κ.ord.ToType) (c : Fin 2)
    {I : SSet.{u}} {F : nerve (AlternatingComponentLower κ (toLex (a, c)) c) ⟶ I}
    (j : JoinCocone F) :
    nerveMap (alternatingComponentLowerToClosed κ (toLex (a, c)) c) ≫
      extendedComponentIndex κ a c j = F := by
  rw [← componentConeIso_inl, extendedComponentIndex, Category.assoc, Iso.hom_inv_id_assoc]
  exact j.property

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
