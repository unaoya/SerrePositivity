module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitCapDiagonalPastingFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitTriangleConeFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.TerminalUnitConeGeometry
/-! # 実六片の単位閉路を四面体の二射影面へ因子分解する

概要：六片の右・左単位辺を、元四面体の終側・始側二面の対角正方形へ同定する。
方針：既存の幾何的な単位面等式を、元入力を固定して全パラメーターへ拡張する。
規約：全正方形の等式を保持し、面の退化はここでは仮定しない。
使われ方：厳密単位則と相対四面体比較を実六片の二閉路へ適用する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

def dgGluingTerminalUnitConeFamily (K : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (K ⊗ Δ[1]) ⟶ Δ[2] ⊗ K :=
  (Δ[1] ◁ (β_ K (Δ[1] : SSet.{u})).hom) ≫
    (α_ (Δ[1] : SSet.{u}) Δ[1] K).inv ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTerminalUnitCone ▷ K)

lemma dgGluingTerminalUnitConeFamily_collapse (K : SSet.{u}) :
    dgGluingTerminalUnitConeFamily K ≫ (stdSimplex.σ (1 : Fin 2) ▷ K) =
      (Δ[1] ◁ fst K (Δ[1] : SSet.{u})) := by
  simp only [dgGluingTerminalUnitConeFamily, Category.assoc]
  rw [← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTerminalUnitCone_collapse]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro p
  rfl

lemma dgGluingUnitCapPastingDomain_first_unit (K : SSet.{u}) :
    (Δ[1] ◁ (β_ K (Δ[1] : SSet.{u})).hom) ≫
      (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain 0 K =
    dgGluingTerminalUnitConeFamily K ≫ (stdSimplex.δ (1 : Fin 4) ▷ K) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[3] ⊗ K) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex_pre,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTriangle_first_unit]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro p
  rfl

lemma dgGluingUnitCapPastingDomain_last_unit (K : SSet.{u}) :
    (Δ[1] ◁ (β_ K (Δ[1] : SSet.{u})).hom) ≫
      (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain 2 K =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitConeFamily K ≫ (stdSimplex.δ (2 : Fin 4) ▷ K) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[3] ⊗ K) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex_pre,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTriangle_last_unit]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro p
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
