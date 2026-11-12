module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CompositionTriangleFamily

/-!
概要：指定された合成三角形を、同じ二辺を固定した延長空間の頂点にする。
方針：内ホーンの二辺に沿う制限を検証し、関手頂点を fiber に制限する。
規約：指定された三角形そのものを使い、充填性による選び直しはしない。
使われ方：元の source 比較の第一三角形を固定する標準頂点。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {X : SSet.{u}} {x y z : X _⦋0⦌}
  {e : X.Edge x y} {f : X.Edge y z} {g : X.Edge x z}

/-- 指定合成三角形の内ホーン制限は、元の二辺を貼ったホーン。 -/
lemma compositionTriangleCompStruct_horn (s : SSet.Edge.CompStruct e f g) :
    (horn 2 1).ι ≫ SSet.yonedaEquiv.symm s.simplex = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn e f := by
  apply horn₂₁.isPushout.hom_ext
  · rw [← Category.assoc, horn.ι_ι, s.δ_two_yonedaEquiv_symm, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn_first]
  · rw [← Category.assoc, horn.ι_ι, s.δ_zero_yonedaEquiv_symm, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn_last]

/-- 指定された同じ合成三角形を、二辺固定の延長空間の頂点として保持する。 -/
def compositionTriangleVertexOfCompStruct (s : SSet.Edge.CompStruct e f g) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace e f) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm s.simplex), by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((horn 2 1).ι ≫ SSet.yonedaEquiv.symm s.simplex) = _
    rw [compositionTriangleCompStruct_horn]
    rfl⟩

/-- 指定頂点への定値族の展開は、元の指定三角形への定値族そのもの。 -/
lemma compositionTriangleVertexOfCompStruct_uncurry {T : SSet.{u}}
    (s : SSet.Edge.CompStruct e f g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerTriangleExtensionUncurry
        (SSet.const (compositionTriangleVertexOfCompStruct s) : T ⟶ _) =
      fst (Δ[2] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm s.simplex := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerTriangleExtensionUncurry
  rw [SSet.const_comp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
