module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.UnitCapUnitLoopDomains
/-! # 単位閉路の全入力輸送と四面体面の可換性

概要：単位閉路の再添字を入力写像で制限しても、同じ単体面を経由する。
方針：入力因子を保持する三つの積写像を全単体上で比較する。
規約：元の正方形と単体面を変更しない。
使われ方：native 単位閉路の評価を主経路の四面体射影へ移す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
lemma dgGluingInitialUnitConeFamily_face_naturality {K P : SSet.{u}} (a : K ⟶ P)
    {n : ℕ} (d : (Δ[2] : SSet.{u}) ⟶ Δ[n]) :
    (Δ[1] ◁ (a ▷ (Δ[1] : SSet.{u}))) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitConeFamily P ≫ (d ▷ P) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitConeFamily K ≫ (d ▷ K) ≫ (Δ[n] ◁ a) := by
  apply SSet.hom_ext
  intro m
  apply ConcreteCategory.hom_ext
  intro p
  rfl

lemma dgGluingTerminalUnitConeFamily_face_naturality {K P : SSet.{u}} (a : K ⟶ P)
    {n : ℕ} (d : (Δ[2] : SSet.{u}) ⟶ Δ[n]) :
    (Δ[1] ◁ (a ▷ (Δ[1] : SSet.{u}))) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTerminalUnitConeFamily P ≫ (d ▷ P) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTerminalUnitConeFamily K ≫ (d ▷ K) ≫ (Δ[n] ◁ a) := by
  apply SSet.hom_ext
  intro m
  apply ConcreteCategory.hom_ext
  intro p
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
