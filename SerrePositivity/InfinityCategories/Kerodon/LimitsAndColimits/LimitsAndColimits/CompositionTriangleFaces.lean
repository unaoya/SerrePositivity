module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CompositionTriangleFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingVertexEquivalence

/-!
概要：元の二辺を固定した三角形の面の等式を、同じ可縮な合成三角形空間へ接続する。
方針：内ホーンの二辺の pushout を全パラメーターとの積で送り、両面の式で制限を確認する。
規約：元の二辺と高次パラメーターを保持する。
使われ方：実際の正方形の最初の三角形を、同じ可縮な空間へ写す。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 区間 Hom の指定頂点への定値族は、その頂点が表す元の辺への定値族。 -/
lemma intervalMappingUncurry_const_vertex {T X : SSet.{u}} {x y : X _⦋0⦌}
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (SSet.const v : T ⟶ _) =
      fst (Δ[1] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex v).edge := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
  rw [SSet.const_comp]
  have hv := congrArg Subtype.val ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeVertexEquiv x y).apply_symm_apply v)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex v).edge) = v.val at hv
  change uncurry (SSet.const v.val) = _
  rw [← hv, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

/-- 三角形の二面が元の二辺に定値なら、内ホーン全体で元の二辺に定値。 -/
lemma compositionTriangleFamily_horn {T X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : X.Edge x y) (f : X.Edge y z) (H : (Δ[2] : SSet.{u}) ⊗ T ⟶ X)
    (h₀ : (stdSimplex.δ (2 : Fin 3) ▷ T) ≫ H =
      fst (Δ[1] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm e.edge)
    (h₁ : (stdSimplex.δ (0 : Fin 3) ▷ T) ≫ H =
      fst (Δ[1] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm f.edge) :
    ((horn 2 1).ι ▷ T) ≫ H = fst (horn 2 1 : SSet.{u}) T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn e f := by
  apply (horn₂₁.isPushout.map (tensorRight T)).hom_ext
  · calc
      (horn₂₁.ι₀₁ ▷ T) ≫ ((horn 2 1).ι ▷ T) ≫ H =
          (stdSimplex.δ (2 : Fin 3) ▷ T) ≫ H := by
        rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι]
      _ = _ := h₀
      _ = (horn₂₁.ι₀₁ ▷ T) ≫ fst (horn 2 1 : SSet.{u}) T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn e f := by
        rw [← Category.assoc, whiskerRight_fst, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn_first]
  · calc
      (horn₂₁.ι₁₂ ▷ T) ≫ ((horn 2 1).ι ▷ T) ≫ H =
          (stdSimplex.δ (0 : Fin 3) ▷ T) ≫ H := by
        rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι]
      _ = _ := h₁
      _ = (horn₂₁.ι₁₂ ▷ T) ≫ fst (horn 2 1 : SSet.{u}) T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn e f := by
        rw [← Category.assoc, whiskerRight_fst, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn_last]

/-- 元の二辺を面として固定した同じ三角形の全族を、可縮な合成三角形空間に戻す。 -/
def compositionTriangleFamilyCurry {T X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : X.Edge x y) (f : X.Edge y z) (H : (Δ[2] : SSet.{u}) ⊗ T ⟶ X)
    (h₀ : (stdSimplex.δ (2 : Fin 3) ▷ T) ≫ H =
      fst (Δ[1] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm e.edge)
    (h₁ : (stdSimplex.δ (0 : Fin 3) ▷ T) ≫ H =
      fst (Δ[1] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm f.edge) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerTriangleExtensionCurry _ H (compositionTriangleFamily_horn e f H h₀ h₁)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
