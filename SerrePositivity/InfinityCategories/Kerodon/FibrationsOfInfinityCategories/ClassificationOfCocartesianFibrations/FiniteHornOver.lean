module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Anodyne.HigherHornEdgeCover
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldFiniteNerveUniverse
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic

/-!
概要：有限単体の nerve 上の実際の内ホーンと、その内 anodyne 性・全辺被覆。
方針：標準ホーン包含に標準単体と有限鎖の nerve の同型を後置する。
規約：三次元以上では全ての退化辺を含めて被覆する。
使われ方：実際の内ホーン上の native Hom と分類先の相対比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 同じ標準ホーンを有限鎖の nerve 上の部分底として表示する。 -/
def cocartesianFiniteHornOver (n : ℕ) (i : Fin (n + 1)) :
    Over (nerve (ULift.{u} (Fin (n + 1)))) :=
  Over.mk ((horn n i).ι ≫ (stdSimplex.isoNerve.{u} n).hom)

/-- 内ホーンの同じ底上の構造射は inner anodyne。 -/
lemma cocartesianFiniteHornOver_innerAnodyne {n : ℕ} (i : Fin (n + 1))
    (h0 : 0 < i) (hi : i < Fin.last n) :
    innerAnodyneExtensions (cocartesianFiniteHornOver.{u} n i).hom :=
  innerAnodyneExtensions.comp_mem _ _ (innerAnodyneExtensions.horn_ι h0 hi)
    (innerAnodyneExtensions.of_isIso _)

/-- 三次元以上では、同じ底上の構造射は実際の全ての辺を覆う。 -/
lemma cocartesianFiniteHornOver_edgeSurjective {n : ℕ} (hn : 3 ≤ n) (i : Fin (n + 1)) :
    Function.Surjective ((cocartesianFiniteHornOver.{u} n i).hom.app (Opposite.op ⦋1⦌)) := by
  change Function.Surjective
    (((stdSimplex.isoNerve.{u} n).hom.app (Opposite.op ⦋1⦌)) ∘
      ((horn n i).ι.app (Opposite.op ⦋1⦌)))
  exact (ConcreteCategory.bijective_of_isIso
    ((stdSimplex.isoNerve.{u} n).hom.app (Opposite.op ⦋1⦌))).2.comp
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horn_ι_edge_surjective_of_three_le hn i)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
