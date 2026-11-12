module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FactorizationTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.Composition

/-!
概要：指定像の二辺による三角形分解から、元の関手の cocartesian 辺保存を反映する。
方針：欠ける底の長辺の同じ cocartesian 持ち上げを二本へ分解する。
規約：元の全空間・関手と長辺を固定する。
使われ方：最初の辺と尾部単体への制限による高次単体の帰納。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 像の二辺で各欠損辺を分解できれば、その像上の辺保存は全ての辺保存を反映する。 -/
lemma preservesCocartesianEdges_of_triangleImage
    {A E F B : SSet.{u}} [Quasicategory B] (a : A ⟶ B)
    (hfactor : ∀ b : B _⦋1⦌, b ∉ Set.range (a.app (Opposite.op ⦋1⦌)) →
      ∃ s : (Δ[2] : SSet.{u}) ⟶ B,
        stdSimplex.δ 1 ≫ s = SSet.yonedaEquiv.symm b ∧
        SSet.yonedaEquiv (stdSimplex.δ 2 ≫ s) ∈ Set.range (a.app (Opposite.op ⦋1⦌)) ∧
        SSet.yonedaEquiv (stdSimplex.δ 0 ≫ s) ∈ Set.range (a.app (Opposite.op ⦋1⦌)))
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (q : F ⟶ B) [InnerFibration q]
    (H : E ⟶ F) (_hH : H ≫ q = p)
    (hpres : ∀ e : E _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p e →
      p.app (Opposite.op ⦋1⦌) e ∈ Set.range (a.app (Opposite.op ⦋1⦌)) →
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (H.app (Opposite.op ⦋1⦌) e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PreservesCocartesianEdges p q H := by
  intro e he
  by_cases hb : p.app (Opposite.op ⦋1⦌) e ∈ Set.range (a.app (Opposite.op ⦋1⦌))
  · exact hpres e he hb
  obtain ⟨s, hs, hsfirst, hssecond⟩ := hfactor _ hb
  have hp : SSet.yonedaEquiv.symm e ≫ p = stdSimplex.δ (1 : Fin 3) ≫ s :=
    (SSet.yonedaEquiv_symm_comp e p).trans hs.symm
  obtain ⟨t, htp, hte, hfirst, hsecond⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_cocartesianFactorizationTriangle p e he s hp
  have hmem (j : Fin 3) :
      p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (stdSimplex.δ j ≫ t)) =
        SSet.yonedaEquiv (stdSimplex.δ j ≫ s) := by
    rw [← SSet.yonedaEquiv_comp, Category.assoc, htp]
  have ha := hpres _ hfirst (by rw [hmem]; exact hsfirst)
  have hc := hpres _ hsecond (by rw [hmem]; exact hssecond)
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_triangle_longEdge (t ≫ H) q
    (by simpa only [← SSet.yonedaEquiv_comp, Category.assoc] using ha)
    (by simpa only [← SSet.yonedaEquiv_comp, Category.assoc] using hc)
  have hv : SSet.yonedaEquiv (stdSimplex.δ 1 ≫ (t ≫ H)) =
      H.app (Opposite.op ⦋1⦌) e := by
    rw [← Category.assoc, hte, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rwa [hv] at hl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
