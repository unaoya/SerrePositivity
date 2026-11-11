module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorPrefixCuts

/-!
# 元の残りの語の制限射の全切断位置

概要：残りの後の全頂点の cut を、切断列の位置を足して元の cut へ戻す。
方針：元の全列の初期区間の特徴付けと切断列の左右での場合分けを使う。
規約：元の頂点番号と空 fiber を保持する。
使われ方：残りの全図式の語の作用への照合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (i : Fin a.length) (hi : a.direction i = .forward)

lemma residual_cut (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)).length + 1)) :
    i.val + ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi).cut
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)) k)).val =
      (f.cut (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualVertex b (f.orderHom i) k)).val := by
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)) k
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualVertex b (f.orderHom i) k
  let p : Fin (a.length + 1) :=
    ⟨i.val + ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi).cut s).val, by
      have hp := ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi).cut s).isLt
      have hiBound := i.isLt
      change ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi).cut s).val < 1 + (a.length - i.val - 1) + 1 at hp
      omega⟩
  have he : p = f.cut t := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.vertex_ext
    intro l
    rw [f.lt_cut_iff]
    by_cases hl : l.val < i.val
    · have hm := f.orderHom.monotone (show l ≤ i by omega)
      change (f.orderHom l).val ≤ (f.orderHom i).val at hm
      constructor
      · intro _
        change (f.orderHom l).val < (f.orderHom i).val + 1 + k.val
        omega
      · intro _
        change l.val < i.val + ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi).cut s).val
        omega
    · let r : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord a i).length := ⟨l.val - i.val, by
        have hl' := l.isLt
        have hi' := i.isLt
        change l.val - i.val < 1 + (a.length - i.val - 1)
        omega⟩
      have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualColumn a i r = l := by
        apply Fin.ext
        change i.val + (l.val - i.val) = l.val
        omega
      have hm := f.orderHom.monotone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.le_residualColumn a i r)
      rw [hr] at hm
      change (f.orderHom i).val ≤ (f.orderHom l).val at hm
      have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi).lt_cut_iff s r
      change l.val - i.val < ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi).cut s).val ↔
        (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualColumn a i r)).val - (f.orderHom i).val < 1 + k.val at hc
      rw [hr] at hc
      change l.val < i.val + ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi).cut s).val ↔
        (f.orderHom l).val < (f.orderHom i).val + 1 + k.val
      omega
  exact congrArg Fin.val he

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.residual_cut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (residual_cut)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
