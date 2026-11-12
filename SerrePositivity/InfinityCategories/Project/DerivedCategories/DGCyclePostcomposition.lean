module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedCompositionLinear

/-! # 閉零 cycle による元の Hom 複体の後合成

概要：元の dg 圏の最後の閉辺による後合成を、全整数次数の鎖写像として構成する。
方針：斉次合成の線形性と Leibniz、閉辺の微分の消滅を使う。
規約：Hom の平坦性や小ささは要求しない。使われ方：最後外ホーンの残差を入れる cone。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 指定閉零 cycle による全次数の後合成鎖写像。 -/
def dgCyclePostcomposition (x : D) {y z : D} (g : _root_.SerrePositivity.DifferentialGraded.zeroCycles (homObject A D y z)) :
    _root_.SerrePositivity.DifferentialGraded.homObject A D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A D x z where
  f k := ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgZeroPostcomposeLinear A D g.val k)
  comm' i j hij := by
    have hj : i + 1 = j := hij
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change differential A (compose A g.val f (add_zero i)) =
      compose A g.val (differential A f) (add_zero (i + 1))
    exact (differential_compose A g.val f (add_zero i)).trans (by
      have hg : differential A g.val = 0 := g.property
      rw [hg, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, zero_add]
      exact one_smul ℤ _)

/-- 後合成鎖写像の各次数成分は、元の通常順斉次合成そのもの。 -/
lemma dgCyclePostcomposition_f (x : D) {y z : D} (g : _root_.SerrePositivity.DifferentialGraded.zeroCycles (homObject A D y z))
    (k : ℤ) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y k) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCyclePostcomposition A D x g).f k f = _root_.SerrePositivity.DifferentialGraded.compose A g.val f (add_zero k) := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
