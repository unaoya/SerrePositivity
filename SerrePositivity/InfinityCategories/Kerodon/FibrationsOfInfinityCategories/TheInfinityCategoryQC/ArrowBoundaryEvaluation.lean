module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ArrowBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：二点からの関手単体集合と二対象の直積の比較。
方針：二頂点の評価と二枝を選ぶ円柱の curry を往復させる。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：二点からの関手単体集合と二対象の直積の比較。
方針：二頂点の評価と二枝を選ぶ円柱の curry を往復させる。
規約：端点の順は始点・終点を保つ。
使われ方：Tamme の lax pullback の構成と普遍性。 -/
def arrowBoundaryEvaluation (C : SSet.{u}) : ((ihom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundary).obj C) ⟶ C ⊗ C :=
  CartesianMonoidalCategory.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ⟨0⟩) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ⟨1⟩)
/-- 概要：二点からの関手単体集合と二対象の直積の比較。
方針：二頂点の評価と二枝を選ぶ円柱の curry を往復させる。
規約：端点の順は始点・終点を保つ。
使われ方：Tamme の lax pullback の構成と普遍性。 -/
def arrowBoundaryFamily (C : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundary ⊗ (C ⊗ C) ⟶ C where
  app d := ↾fun z ↦ Fin.cases z.2.1 (fun _ ↦ z.2.2) z.1.down
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨i⟩, x, y⟩
    fin_cases i <;> rfl
/-- 概要：二点からの関手単体集合と二対象の直積の比較。
方針：二頂点の評価と二枝を選ぶ円柱の curry を往復させる。
規約：端点の順は始点・終点を保つ。
使われ方：Tamme の lax pullback の構成と普遍性。 -/
def arrowBoundaryEvaluationInv (C : SSet.{u}) : C ⊗ C ⟶ (ihom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundary).obj C :=
  curry (arrowBoundaryFamily C)
/-- 概要：二点からの関手単体集合と二対象の直積の比較。
方針：二頂点の評価と二枝を選ぶ円柱の curry を往復させる。
規約：端点の順は始点・終点を保つ。
使われ方：Tamme の lax pullback の構成と普遍性。 -/
lemma arrowBoundaryEvaluation_hom_inv (C : SSet.{u}) :
    arrowBoundaryEvaluation C ≫ arrowBoundaryEvaluationInv C = 𝟙 _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro t
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  rintro ⟨i⟩
  fin_cases i
  · change C.map α (t.app n (𝟙 n) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundary) ⟨0⟩ n.unop.len)) =
      t.app d α ⟨0⟩
    have h := ConcreteCategory.congr_hom (t.naturality α (𝟙 n)) (⟨0⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundary.obj n)
    change t.app d (𝟙 n ≫ α) ⟨0⟩ = C.map α (t.app n (𝟙 n) ⟨0⟩) at h
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundary_constant, Category.id_comp, Category.comp_id] using h.symm
  · change C.map α (t.app n (𝟙 n) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundary) ⟨1⟩ n.unop.len)) =
      t.app d α ⟨1⟩
    have h := ConcreteCategory.congr_hom (t.naturality α (𝟙 n)) (⟨1⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundary.obj n)
    change t.app d (𝟙 n ≫ α) ⟨1⟩ = C.map α (t.app n (𝟙 n) ⟨1⟩) at h
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundary_constant, Category.id_comp, Category.comp_id] using h.symm
/-- 概要：二点からの関手単体集合と二対象の直積の比較。
方針：二頂点の評価と二枝を選ぶ円柱の curry を往復させる。
規約：端点の順は始点・終点を保つ。
使われ方：Tamme の lax pullback の構成と普遍性。 -/
lemma arrowBoundaryEvaluation_inv_hom (C : SSet.{u}) :
    arrowBoundaryEvaluationInv C ≫ arrowBoundaryEvaluation C = 𝟙 _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, y⟩
  change (C.map (𝟙 n) x, C.map (𝟙 n) y) = (x, y)
  rw [CategoryTheory.Functor.map_id]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
