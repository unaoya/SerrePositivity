module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.UnitCapGeometry

/-! # 全入力を保つ標準合成面への単位補正

概要：補正済み角と標準合成面の間を、元固定辺と一定可変辺を保ってつなぐ。
方針：共通の時間再添字を有限単調写像へ適用し、対称な単位側面を消去する。
規約：区間全体の固定条件を保持する。使われ方：選択済み合成変形へ相対比較を移す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
lemma dgGluingFirstUnitCapFamily_first {Z K : SSet.{u}}
    (T : (Δ[1] : SSet.{u}) ⊗ (Δ[2] ⊗ K) ⟶ Z) (e : (Δ[1] : SSet.{u}) ⟶ Z)
    (hs : (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) ≫ T =
      (Δ[1] ◁ fst (Δ[1] : SSet.{u}) K) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSquareUnitCollapse 0 ≫ e) :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap ≫ T) =
      fst (Δ[1] : SSet.{u}) (K ⊗ Δ[1]) ≫ e := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex_pre, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap_first,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex_post, Category.assoc, hs]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex_forget, Category.assoc,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollarSide ≫ (β_ (Δ[1] : SSet.{u}) Δ[1]).hom)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSquareUnitCollapse 0) e,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCapSide_collapse]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl


lemma dgGluingFirstUnitCapFamily_last {K : SSet.{u}} :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap =
    (Δ[1] ◁ fst K (Δ[1] : SSet.{u})) ≫ (stdSimplex.δ (0 : Fin 3) ▷ K) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[2] ⊗ K) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex_pre, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap_last]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
lemma dgGluingLastUnitCapFamily_last {Z K : SSet.{u}}
    (T : (Δ[1] : SSet.{u}) ⊗ (Δ[2] ⊗ K) ⟶ Z) (e : (Δ[1] : SSet.{u}) ⟶ Z)
    (hs : (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫ T =
      (Δ[1] ◁ fst (Δ[1] : SSet.{u}) K) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSquareUnitCollapse 1 ≫ e) :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap ≫ T) =
      fst (Δ[1] : SSet.{u}) (K ⊗ Δ[1]) ≫ e := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex_pre, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap_last,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex_post, Category.assoc, hs]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex_forget, Category.assoc,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollarSide ≫ (β_ (Δ[1] : SSet.{u}) Δ[1]).hom)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSquareUnitCollapse 1) e,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCapSide_collapse]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl


lemma dgGluingLastUnitCapFamily_first {K : SSet.{u}} :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap =
    (Δ[1] ◁ fst K (Δ[1] : SSet.{u})) ≫ (stdSimplex.δ (2 : Fin 3) ▷ K) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[2] ⊗ K) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex_pre, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap_first]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl


lemma dgGluingFirstUnitCapFamily_zero {K : SSet.{u}} :
    (Δ[2] ◁ (ι₀ : K ⟶ _)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap =
      (Δ[2] ◁ (ι₀ : K ⟶ _)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollar := by
  calc
    _ = ((ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap) ▷ K) ≫
        (α_ (Δ[1] : SSet.{u}) Δ[2] K).hom := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap_zero]
      rfl

lemma dgGluingFirstUnitCapFamily_one {K : SSet.{u}} :
    (Δ[2] ◁ (ι₁ : K ⟶ _)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[2] ⊗ K) := by
  calc
    _ = ((ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap) ▷ K) ≫
        (α_ (Δ[1] : SSet.{u}) Δ[2] K).hom := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap_one]
      rfl

lemma dgGluingLastUnitCapFamily_zero {K : SSet.{u}} :
    (Δ[2] ◁ (ι₀ : K ⟶ _)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[2] ⊗ K) := by
  calc
    _ = ((ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap) ▷ K) ≫
        (α_ (Δ[1] : SSet.{u}) Δ[2] K).hom := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap_zero]
      rfl

lemma dgGluingLastUnitCapFamily_one {K : SSet.{u}} :
    (Δ[2] ◁ (ι₁ : K ⟶ _)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap =
      (Δ[2] ◁ (ι₁ : K ⟶ _)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar := by
  calc
    _ = ((ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap) ▷ K) ≫
        (α_ (Δ[1] : SSet.{u}) Δ[2] K).hom := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap_one]
      rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
