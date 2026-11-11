module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitCapDiagonalPastingGeometry
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.PrismParameterReindex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitCollarDiagonalTriangleFamilies
/-! # 係数側の六三角形の共有辺と端点退化を全入力へ輸送する

概要：六つの有限貼り合わせ片を元入力全体へ拡張し、共有辺と既知の端点固定を保持する。
方針：同じ prism 再添字の面・後合成・端点退化の自然性を使う。
規約：入力や幾何片を変更せず、単位則はこの再添字に仮定しない。
使われ方：六片を同じ native augmentation 四面体へ接続する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

def dgGluingUnitCapPastingDomain (i : Fin 6) (K : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTriangle i) K

lemma dgGluingUnitCapPastingDomain_first_diagonal (K : SSet.{u}) :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ K)) ≫ dgGluingUnitCapPastingDomain 0 K =
      (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ K)) ≫ dgGluingUnitCapPastingDomain 1 K := by
  simp only [dgGluingUnitCapPastingDomain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex_pre,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTriangle_first_diagonal]

lemma dgGluingUnitCapPastingDomain_last_diagonal (K : SSet.{u}) :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ K)) ≫ dgGluingUnitCapPastingDomain 2 K =
      (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ K)) ≫ dgGluingUnitCapPastingDomain 3 K := by
  simp only [dgGluingUnitCapPastingDomain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex_pre,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTriangle_last_diagonal]

lemma dgGluingUnitCapPastingDomain_first_bridge (K : SSet.{u}) :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) ≫ dgGluingUnitCapPastingDomain 1 K =
      (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) ≫ dgGluingUnitCapPastingDomain 5 K := by
  simp only [dgGluingUnitCapPastingDomain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex_pre,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTriangle_first_bridge]

lemma dgGluingUnitCapPastingDomain_last_bridge (K : SSet.{u}) :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫ dgGluingUnitCapPastingDomain 3 K =
      (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫ dgGluingUnitCapPastingDomain 5 K := by
  simp only [dgGluingUnitCapPastingDomain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex_pre,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTriangle_last_bridge]

lemma dgGluingUnitCapPastingDomain_coefficient_first (K : SSet.{u}) :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫ dgGluingUnitCapPastingDomain 1 K =
      (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫ dgGluingUnitCapPastingDomain 4 K := by
  simp only [dgGluingUnitCapPastingDomain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex_pre,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTriangle_coefficient_first]

lemma dgGluingUnitCapPastingDomain_coefficient_last (K : SSet.{u}) :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) ≫ dgGluingUnitCapPastingDomain 3 K =
      (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) ≫ dgGluingUnitCapPastingDomain 4 K := by
  simp only [dgGluingUnitCapPastingDomain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex_pre,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTriangle_coefficient_last]

lemma dgGluingUnitCapPastingDomain_collar_bridge (K : SSet.{u}) :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ K)) ≫ dgGluingUnitCapPastingDomain 5 K =
      (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ K)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarDiagonalTriangleDomain K := by
  change _ = (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ K)) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarDiagonalTriangle K
  simp only [dgGluingUnitCapPastingDomain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex_pre,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTriangle_collar_bridge]

lemma dgGluingUnitCapPastingDomain_first_cap (K : SSet.{u}) :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) ≫ dgGluingUnitCapPastingDomain 0 K =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{u}) K).hom) ≫
        (stdSimplex.δ (1 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap ≫
            (Δ[1] ◁ (stdSimplex.δ (3 : Fin 4) ▷ K)) := by
  simp only [dgGluingUnitCapPastingDomain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex_pre,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTriangle_first_cap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex_post,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex_triangle_diagonal]

lemma dgGluingUnitCapPastingDomain_last_cap (K : SSet.{u}) :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫ dgGluingUnitCapPastingDomain 2 K =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{u}) K).hom) ≫
        (stdSimplex.δ (1 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap ≫
            (Δ[1] ◁ (stdSimplex.δ (0 : Fin 4) ▷ K)) := by
  simp only [dgGluingUnitCapPastingDomain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex_pre,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTriangle_last_cap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex_post,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex_triangle_diagonal]

lemma dgGluingUnitCapPastingDomain_source_retract (i : Fin 6) (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[2] ⊗ K) ≫ dgGluingUnitCapPastingDomain i K =
      (stdSimplex.σ ((![1, 0, 1, 0, 0, 0] : Fin 6 → Fin 2) i) ▷ K) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ K) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingSourceSide i) K :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex_endpoint_retract _ _ K 0 _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTriangle_source_retract i)

lemma dgGluingUnitCapPastingDomain_target_retract (i : Fin 6) (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[2] ⊗ K) ≫ dgGluingUnitCapPastingDomain i K =
      (stdSimplex.σ ((![0, 1, 0, 1, 1, 1] : Fin 6 → Fin 2) i) ▷ K) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] ⊗ K) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTargetSide i) K :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex_endpoint_retract _ _ K 1 _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTriangle_target_retract i)

lemma dgGluingUnitCapPastingSourceSide_reindex (i : Fin 6) (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingSourceSide i) K =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{u}) K).hom) ≫
        (stdSimplex.δ (1 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex
            (if i = 0 ∨ i = 1 ∨ i = 4 then _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap else _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollar) ≫
              (Δ[1] ◁ (stdSimplex.δ (3 : Fin 4) ▷ K)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingSourceSide, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex_post,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex_triangle_diagonal]

lemma dgGluingUnitCapPastingTargetSide_reindex (i : Fin 6) (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTargetSide i) K =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{u}) K).hom) ≫
        (stdSimplex.δ (1 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex
            (if i = 2 ∨ i = 3 ∨ i = 4 then _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap else _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar) ≫
              (Δ[1] ◁ (stdSimplex.δ (0 : Fin 4) ▷ K)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTargetSide, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex_post,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex_triangle_diagonal]

lemma dgGluingUnitCapPastingDomain_coefficient_diagonal (K : SSet.{u}) :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ K)) ≫ dgGluingUnitCapPastingDomain 4 K =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex (β_ (Δ[1] : SSet.{u}) Δ[1]).hom K ≫
        (Δ[1] ◁ ((stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4)) ▷ K)) := by
  rw [dgGluingUnitCapPastingDomain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex_pre,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTriangle_coefficient_diagonal, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex_post]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
