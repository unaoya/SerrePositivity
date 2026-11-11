module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.StrictDiagramMappingEvaluation

/-!
概要：weighted nerve の追加パラメーターを係数図式のテンソル因子へ移す。
方針：各初区間で係数と同じパラメーター単体の制限を対にする。
規約：パラメーターの Kan 性を要求しない。
使われ方：Kerodon §§5.3.3（Tag 025W）、5.6.5（Tag 028U）、weighted nerve の高次の変換への作用と境界付き比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：weighted nerve の係数の初区間図式に同じ単体パラメーターを添える。
方針：重みの各成分を係数の成分とパラメーターの初区間への制限の対で写す。
規約：底の射列を保持する。
使われ方：Kerodon §5.3.3（Tag 025W）、パラメーター付きの係数の変換を評価する入力。 -/
def weightedNerveTensorDiagram {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (T : SSet.{u}) {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n) (t : T _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ s.1 ⋙ F ⋙ tensorRight T where
  app i := lift (s.2.app i)
    (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)) ≫
      SSet.yonedaEquiv.symm t)
  naturality i j f := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    apply Prod.ext
    · exact ConcreteCategory.congr_hom (NatTrans.congr_app (s.2.naturality f) d) z
    · have h : stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val j.val (leOfHom f)) ≫
          (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)) ≫
            SSet.yonedaEquiv.symm t) =
        stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)) ≫
          SSet.yonedaEquiv.symm t := by
        rw [← Category.assoc, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_comp]
      exact ConcreteCategory.congr_hom (NatTrans.congr_app h d) z

/-- 概要：weighted nerve の追加パラメーターを係数のテンソル因子へ移す射。
方針：底の射列を保ち、各係数の初区間図式をパラメーターとの対に置き換える。
規約：任意の単体集合 T に対する全次数の射。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な変換空間全体で weighted nerve を評価する準備。 -/
def weightedNerveTensorMap {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (T : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F ⊗ T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (F ⋙ tensorRight T) where
  app _ := ↾fun ⟨s, t⟩ ↦ ⟨s.1, weightedNerveTensorDiagram F T s t⟩
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨σ, τ⟩, t⟩
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    apply NatTrans.ext
    funext i
    change lift (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α.unop i) ≫ τ.app _)
        (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val m.unop.len _) ≫
          SSet.yonedaEquiv.symm (T.map α t)) =
      stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α.unop i) ≫
        lift (τ.app _) (stdSimplex.map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion (α.unop.toOrderHom i).val n.unop.len _) ≫ SSet.yonedaEquiv.symm t)
    rw [comp_lift]
    apply congrArg (fun r ↦ lift
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α.unop i) ≫ τ.app _) r)
    have hy : SSet.yonedaEquiv.symm (T.map α t) =
        stdSimplex.map α.unop ≫ SSet.yonedaEquiv.symm t :=
      (SSet.yonedaEquiv_symm_naturality_left α.unop t).symm
    rw [hy, ← Category.assoc, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction_factor,
      Functor.map_comp, Category.assoc]

/-- 概要：パラメーターを係数へ移す射は元の底への射影を保持する。
方針：weighted nerve の底の射列だけを読む。
規約：追加のパラメーターは底では忘れる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対写像空間への高次の作用を curry するための条件。 -/
lemma weightedNerveTensorMap_projection {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (T : SSet.{u}) :
    weightedNerveTensorMap F T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (F ⋙ tensorRight T) =
      fst (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
