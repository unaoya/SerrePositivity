module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomotopyIntervalPath
/-! # 同じ全円柱写像を持つ変形の区間 path の一致

概要：端点表示が異なっても、全円柱写像が一致する変形は同じ区間 path を与える。
方針：固定した因子交換と curry に元の射の等式を適用する。
規約：端点輸送の証明を展開せず、全時間の射の等式を使う。
使われ方：正本の二つの path 比較を、検証可能な小さな段階で照合する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
lemma dgGluingHomotopyIntervalPath_eq_of_h_eq {K Z : SSet.{u}}
    {a b c d : K ⟶ Z} (H : SSet.Homotopy a b) (G : SSet.Homotopy c d)
    (h : H.h = G.h) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyIntervalPath H = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyIntervalPath G :=
  congrArg (fun k => curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫ k)) h
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
