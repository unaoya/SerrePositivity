module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitCapGeometry

/-! # 全入力を保つ標準合成面への単位補正

概要：補正済み角と標準合成面の間を、元固定辺と一定可変辺を保ってつなぐ。
方針：共通の時間再添字を有限単調写像へ適用し、対称な単位側面を消去する。
規約：区間全体の固定条件を保持する。使われ方：選択済み合成変形へ相対比較を移す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
lemma dgGluingFirstUnitCapFamily_first {Z K : SSet.{u}}
    (T : (Δ[1] : SSet.{u}) ⊗ (Δ[2] ⊗ K) ⟶ Z) (e : (Δ[1] : SSet.{u}) ⟶ Z)
    (hs : (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) ≫ T =
      (Δ[1] ◁ fst (Δ[1] : SSet.{u}) K) ≫ dgGluingSquareUnitCollapse 0 ≫ e) :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      (dgGluingTriangleTimeReindex dgGluingFirstUnitCap ≫ T) =
      fst (Δ[1] : SSet.{u}) (K ⊗ Δ[1]) ≫ e := by
  rw [← Category.assoc, dgGluingTriangleTimeReindex_pre, dgGluingFirstUnitCap_first,
    dgGluingTriangleTimeReindex_post, Category.assoc, hs]
  rw [← Category.assoc, dgGluingTriangleTimeReindex_forget, Category.assoc,
    ← Category.assoc (dgGluingFirstUnitCollarSide ≫ (β_ (Δ[1] : SSet.{u}) Δ[1]).hom)
      (dgGluingSquareUnitCollapse 0) e,
    dgGluingFirstUnitCapSide_collapse]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl


lemma dgGluingFirstUnitCapFamily_last {K : SSet.{u}} :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      dgGluingTriangleTimeReindex dgGluingFirstUnitCap =
    (Δ[1] ◁ fst K (Δ[1] : SSet.{u})) ≫ (stdSimplex.δ (0 : Fin 3) ▷ K) ≫
      prismEndpoint 1 (Δ[2] ⊗ K) := by
  rw [dgGluingTriangleTimeReindex_pre, dgGluingFirstUnitCap_last]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
lemma dgGluingLastUnitCapFamily_last {Z K : SSet.{u}}
    (T : (Δ[1] : SSet.{u}) ⊗ (Δ[2] ⊗ K) ⟶ Z) (e : (Δ[1] : SSet.{u}) ⟶ Z)
    (hs : (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫ T =
      (Δ[1] ◁ fst (Δ[1] : SSet.{u}) K) ≫ dgGluingSquareUnitCollapse 1 ≫ e) :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      (dgGluingTriangleTimeReindex dgGluingLastUnitCap ≫ T) =
      fst (Δ[1] : SSet.{u}) (K ⊗ Δ[1]) ≫ e := by
  rw [← Category.assoc, dgGluingTriangleTimeReindex_pre, dgGluingLastUnitCap_last,
    dgGluingTriangleTimeReindex_post, Category.assoc, hs]
  rw [← Category.assoc, dgGluingTriangleTimeReindex_forget, Category.assoc,
    ← Category.assoc (dgGluingLastUnitCollarSide ≫ (β_ (Δ[1] : SSet.{u}) Δ[1]).hom)
      (dgGluingSquareUnitCollapse 1) e,
    dgGluingLastUnitCapSide_collapse]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl


lemma dgGluingLastUnitCapFamily_first {K : SSet.{u}} :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      dgGluingTriangleTimeReindex dgGluingLastUnitCap =
    (Δ[1] ◁ fst K (Δ[1] : SSet.{u})) ≫ (stdSimplex.δ (2 : Fin 3) ▷ K) ≫
      prismEndpoint 0 (Δ[2] ⊗ K) := by
  rw [dgGluingTriangleTimeReindex_pre, dgGluingLastUnitCap_first]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl


lemma dgGluingFirstUnitCapFamily_zero {K : SSet.{u}} :
    (Δ[2] ◁ (ι₀ : K ⟶ _)) ≫
      dgGluingTriangleTimeReindex dgGluingFirstUnitCap =
      (Δ[2] ◁ (ι₀ : K ⟶ _)) ≫ dgGluingTriangleTimeReindex dgGluingFirstUnitCollar := by
  calc
    _ = ((ι₀ ≫ dgGluingFirstUnitCap) ▷ K) ≫
        (α_ (Δ[1] : SSet.{u}) Δ[2] K).hom := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by
      rw [dgGluingFirstUnitCap_zero]
      rfl

lemma dgGluingFirstUnitCapFamily_one {K : SSet.{u}} :
    (Δ[2] ◁ (ι₁ : K ⟶ _)) ≫
      dgGluingTriangleTimeReindex dgGluingFirstUnitCap =
      prismEndpoint 1 (Δ[2] ⊗ K) := by
  calc
    _ = ((ι₁ ≫ dgGluingFirstUnitCap) ▷ K) ≫
        (α_ (Δ[1] : SSet.{u}) Δ[2] K).hom := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by
      rw [dgGluingFirstUnitCap_one]
      rfl

lemma dgGluingLastUnitCapFamily_zero {K : SSet.{u}} :
    (Δ[2] ◁ (ι₀ : K ⟶ _)) ≫
      dgGluingTriangleTimeReindex dgGluingLastUnitCap =
      prismEndpoint 0 (Δ[2] ⊗ K) := by
  calc
    _ = ((ι₀ ≫ dgGluingLastUnitCap) ▷ K) ≫
        (α_ (Δ[1] : SSet.{u}) Δ[2] K).hom := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by
      rw [dgGluingLastUnitCap_zero]
      rfl

lemma dgGluingLastUnitCapFamily_one {K : SSet.{u}} :
    (Δ[2] ◁ (ι₁ : K ⟶ _)) ≫
      dgGluingTriangleTimeReindex dgGluingLastUnitCap =
      (Δ[2] ◁ (ι₁ : K ⟶ _)) ≫ dgGluingTriangleTimeReindex dgGluingLastUnitCollar := by
  calc
    _ = ((ι₁ ≫ dgGluingLastUnitCap) ▷ K) ≫
        (α_ (Δ[1] : SSet.{u}) Δ[2] K).hom := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by
      rw [dgGluingLastUnitCap_one]
      rfl
end SerrePositivity.InfinityCategories
