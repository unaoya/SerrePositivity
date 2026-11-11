module

public import
  SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoCoherence

/-!
概要：充満忠実な射への像で指定同型の値が一致すれば、元の全族でも同じ指定値を回収する。
方針：元の両端の等号を消去して、指定同型の等式を充満忠実に反映する。
規約：元の全族と指定同型の値を保持する。
使われ方：終点 slice 比較の旧族での一致を、元の実 comma の指定比較へ戻す。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：元の端点の等号と充満忠実な像の指定値の一致は、元の指定同型の値を反映する。
方針：同じ端点で等式を反映。規約：指定値を保持。使われ方：実 comma への相対反映。 -/
lemma fullyFaithful_reflects_functorIso_heq {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful p)
    {f g f' g' : A ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g')
    (hf : f = f') (hg : g = g') (he : HEq (e.postcomp p) (e'.postcomp p)) :
    HEq e e' := by
  cases hf
  cases hg
  exact heq_of_eq (hp.postcomp_functorIso_injective e e' (eq_of_heq he))
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
