module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.AdjointRepresentability

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeAdjointFunctorCriterion
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RepresentableInversionLocality
public import Mathlib.Tactic.CrossRefAttribute

/-!
presentable ∞ 圏の関手について、右随伴の存在と小余極限保存を比較する。Kerodon 9.5.2.1（Tag 06Q5）。HTT 5.5.2.9。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：presentable 圏の関手が右随伴を持つことは全小余極限保存と同値。
方針：小さい反変 Hom 合成を表現し、元の全随伴を構成する。
規約：比較界面や一般局所化の存在を追加入力にしない。
使われ方：HTT 5.5.2.9、Pr^L の随伴による特徴づけ。 -/
@[kerodon 06Q5]
lemma exists_rightAdjoint_iff_preservesSmallColimits
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable D) (L : C ⟶ D) :
    (∃ R : D ⟶ C, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)) ↔ _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits L :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits_of_inversionLocality
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presheaf_representableInversionDetectsLocality hC hD L

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.2.3.6" (partial := special) "仮定：C,D が presentable、準圏間の関手 f（Lean が強い：本文の「適切な集合論的仮定」のうち presentable の場合）。結論：f の右随伴の存在と全小余極限保存の同値（この場合に一致）。単なる余極限保存から無条件に右随伴を得る主張としては読まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits
attribute [cite HTT "5.2.6.1" (partial := stronger-hyp) "仮定：C,D が presentable（Lean が強い：原典の任意の準圏にこの仮定を追加）。結論：左右随伴の存在で頂点を選ぶ FunL(C,D),FunR(C,D) の全部分準圏（この場合に一致）。PrL は全小余極限保存、PrR は accessible かつ全小極限保存で定義され、二つの存在判定の同値により同じ頂点条件となる。core だけには制限していない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits
attribute [cite HTT "5.2.6.2" (partial := stronger-hyp) "仮定：C,D が presentable（Lean が強い：任意の準圏の場合は含まない）。結論：FunL(C,D) と FunR(D,C)op の全準圏の同値で、同値の順方向の各値は元の左関手の右随伴（この場合に一致）。PrL/PrR の頂点条件と随伴存在の同値も併用する。非可逆な自然変換と全高次単体を保持し、右随伴の対象ごとの選択だけでは代用しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits
attribute [cite HTT "5.5.2.9"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits
