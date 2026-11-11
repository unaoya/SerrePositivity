module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveConstantEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveFiber

/-!
概要：定値係数の weighted nerve へ、底の nerve と係数の直積から写す。
方針：底の射列と、同じ係数単体の初区間への制限の図式を組にする。
規約：係数の Kan 性は不要。
使われ方：Kerodon §5.3.3（Tag 025W）、係数の射を weighted nerve の transport として表示する prism の構成。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：底の射列と係数単体から定値係数の weighted nerve の単体を作る。
方針：各初区間の係数は同じ単体の制限とする。
規約：出力の底の射列は入力の射列をそのまま使う。
使われ方：Kerodon §5.3.3（Tag 025W）、定値係数の評価の逆向きの構成。 -/
def weightedNerveConstantProduct (C : Type u) [Category.{u} C] (K : SSet.{u}) :
    nerve C ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve ((CategoryTheory.Functor.const C).obj K) where
  app d := ↾fun ⟨σ, x⟩ ↦ ⟨σ,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantDiagram ((CategoryTheory.Functor.const C).obj K) (σ.obj 0) x⟩
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, x⟩
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    apply NatTrans.ext
    funext i
    change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val e.unop.len _) ≫
        SSet.yonedaEquiv.symm (K.map α x) =
      stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α.unop i) ≫
        (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion (α.unop.toOrderHom i).val d.unop.len _) ≫
          SSet.yonedaEquiv.symm x)
    have hy : SSet.yonedaEquiv.symm (K.map α x) =
        stdSimplex.map α.unop ≫ SSet.yonedaEquiv.symm x :=
      (SSet.yonedaEquiv_symm_naturality_left (X := K) α.unop x).symm
    rw [hy, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction_factor,
      CategoryTheory.Functor.map_comp, Category.assoc]

/-- 概要：定値係数の直積からの射は底への第一射影を被覆する。
方針：weighted nerve の単体の底の射列を計算する。
規約：底は通常の圏の nerve。
使われ方：Kerodon §5.3.3（Tag 025W）、transport の prism の底上の可換性。 -/
lemma weightedNerveConstantProduct_projection (C : Type u) [Category.{u} C] (K : SSet.{u}) :
    weightedNerveConstantProduct C K ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection ((CategoryTheory.Functor.const C).obj K) = fst (nerve C) K := rfl

/-- 概要：定値係数の直積からの射を底の一点に制限すると標準の定値包含。
方針：底の射列が定値となることと係数図式の定義を計算する。
規約：係数因子は恒等射で保持する。
使われ方：Kerodon §5.3.3（Tag 025W）、transport の始点・終点での値の計算。 -/
lemma weightedNerveConstantProduct_at {C : Type u} [Category.{u} C] (K : SSet.{u}) (c : C) :
    lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) (𝟙 K) ≫ weightedNerveConstantProduct C K =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift ((CategoryTheory.Functor.const C).obj K) c := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
