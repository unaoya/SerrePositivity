module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.PullbackCompatibleFunctorIso

/-!
概要：共有端点の同じ表示で指定像が一致する二成分を pullback の関手同型へ束ねる。
方針：共通の端点正規化を二成分の直接比較へ移し、両端固定の代表辺を貼り合わせる。
規約：全パラメーターと元の二つの成分同型を保持し、pullback の Kan 性を要求しない。
使われ方：補正成分の同じ共有頂点での整合を実際の pullback 比較へ渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks

/-- 共通の端点正規化での一致は、片方の端点へ直接揃えた指定値の一致を与える。 -/
lemma functorIsoOfEq_eq_of_common_normalization {A Y : SSet.{u}}
    {a b c d x y : A ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c d)
    (ha : a = x) (hb : b = y) (hc : c = x) (hd : d = y)
    (h : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e ha hb = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e' hc hd) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e (ha.trans hc.symm) (hb.trans hd.symm) = e' := by
  subst x y c d
  have hh : HEq e e' := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq e rfl rfl).symm.trans
    ((heq_of_eq h).trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq e' rfl rfl))
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq e rfl rfl).trans hh)

/-- 共通端点での指定像の一致から、同じ二射の間の pullback の関手同型を作る。 -/
def pullbackFunctorIsoOfCommonNormalizedIsos {A X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    (f : X ⟶ Z) (g : Y ⟶ Z) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration f]
    (a b : A ⟶ pullback f g)
    (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a ≫ pullback.fst f g) (b ≫ pullback.fst f g))
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a ≫ pullback.snd f g) (b ≫ pullback.snd f g))
    {x y : A ⟶ Z}
    (hL₀ : ((a ≫ pullback.fst f g) ≫ f) = x)
    (hL₁ : ((b ≫ pullback.fst f g) ≫ f) = y)
    (hR₀ : ((a ≫ pullback.snd f g) ≫ g) = x)
    (hR₁ : ((b ≫ pullback.snd f g) ≫ g) = y)
    (h : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (L.postcomp f) hL₀ hL₁ =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (R.postcomp g) hR₀ hR₁) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackFunctorIsoOfCompatibleIsos f g a b L R
    (functorIsoOfEq_eq_of_common_normalization (L.postcomp f) (R.postcomp g)
      hL₀ hL₁ hR₀ hR₁ h)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks
