module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback

/-! # slice の指定頂点の錐の回収

概要：slice 境界の最後の頂点に指定した錐を、join の境界写像の制限として回収する。
方針：uncurry の Yoneda 射による評価と前合成の自然性を使う。
規約：HTT §1.2.13。使われ方：N7c の錐の対象・脚・三角形成分と境界データの比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite
open scoped _root_.Simplicial

/-- 概要：slice の一単体の Yoneda 射を uncurry すると、その単体に付いた join の射になる。
方針：恒等射の uncurry の各単体の Yoneda 制限の評価式を使う。
規約：HTT §1.2.13。使われ方：指定された零単体の錐を join の写像として復元する。 -/
lemma sliceOverUncurry_yoneda {K X : SSet.{u}} {p : K ⟶ X} {n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (SSet.yonedaEquiv.symm c) = c.val := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) (SSet.yonedaEquiv.symm c)
  simp only [Category.comp_id] at h
  rw [h]
  apply SSet.hom_ext
  intro d
  rcases d with ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurryApp_yoneda (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) c s

/-- 概要：境界の最後の頂点が指定された錐なら、uncurry した境界写像のその頂点の join は錐に等しい。
方針：最後の頂点への制限の等式を uncurry し、前合成と Yoneda の公式を使う。
規約：HTT §1.2.13。使われ方：標準 fiber の脚とホモトピーを実際の境界から回収する。 -/
lemma sliceBoundary_last_cone {K X : SSet.{u}} {p : K ⟶ X} {n : ℕ}
    (b : (SSet.boundary (n + 1) : SSet) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b = SSet.yonedaEquiv.symm c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1))) (𝟙 K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b = c.val := by
  have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry hb
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, sliceOverUncurry_yoneda] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
