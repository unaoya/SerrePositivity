module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitTriangleConeGeometry
/-! # 単位三角形の対角閉路を元入力全体へ拡張する

概要：単位三角形の対角正方形を全入力へ拡張し、四辺と退化の場合の全時間を保持する。
方針：位相・入力因子を交換するだけで有限再添字を輸送する。
規約：四辺の厳密な因子分解を使い、端点だけの一致で代用しない。
使われ方：相対四面体比較から左単位対角の相対二次元比較を取り出す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

def dgGluingInitialUnitConeFamily (K : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (K ⊗ Δ[1]) ⟶ Δ[2] ⊗ K :=
  (Δ[1] ◁ (β_ K (Δ[1] : SSet.{u})).hom) ≫
    (α_ (Δ[1] : SSet.{u}) Δ[1] K).inv ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitCone ▷ K)

lemma dgGluingInitialUnitConeFamily_source (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (K ⊗ Δ[1]) ≫ dgGluingInitialUnitConeFamily K =
      (β_ K (Δ[1] : SSet.{u})).hom ≫ (stdSimplex.δ (2 : Fin 3) ▷ K) := by
  calc
    _ = (β_ K (Δ[1] : SSet.{u})).hom ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitCone) ▷ K) := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitCone_source]

lemma dgGluingInitialUnitConeFamily_target (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (K ⊗ Δ[1]) ≫ dgGluingInitialUnitConeFamily K =
      fst K (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫
        (stdSimplex.δ (0 : Fin 3) ▷ K) := by
  calc
    _ = (β_ K (Δ[1] : SSet.{u})).hom ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitCone) ▷ K) := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitCone_target]
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl

lemma dgGluingInitialUnitConeFamily_zero (K : SSet.{u}) :
    (Δ[1] ◁ (ι₀ : K ⟶ _)) ≫ dgGluingInitialUnitConeFamily K =
      stdSimplex.δ (1 : Fin 3) ▷ K := by
  calc
    _ = (((ι₀ : (Δ[1] : SSet.{u}) ⟶ _) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitCone) ▷ K) := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitCone_zero]

lemma dgGluingInitialUnitConeFamily_one (K : SSet.{u}) :
    (Δ[1] ◁ (ι₁ : K ⟶ _)) ≫ dgGluingInitialUnitConeFamily K =
      stdSimplex.δ (0 : Fin 3) ▷ K := by
  calc
    _ = (((ι₁ : (Δ[1] : SSet.{u}) ⟶ _) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitCone) ▷ K) := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitCone_one]

lemma dgGluingInitialUnitConeFamily_collapse (K : SSet.{u}) :
    dgGluingInitialUnitConeFamily K ≫ (stdSimplex.σ (0 : Fin 2) ▷ K) =
      (Δ[1] : SSet.{u}) ◁ fst K (Δ[1] : SSet.{u}) := by
  calc
    _ = (Δ[1] ◁ (β_ K (Δ[1] : SSet.{u})).hom) ≫
        (α_ (Δ[1] : SSet.{u}) Δ[1] K).inv ≫
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitCone ≫ stdSimplex.σ (0 : Fin 2)) ▷ K) := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitCone_collapse]
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
