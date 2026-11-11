module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareTopMiddleHomotopy
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FixedMapHomotopyEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport

/-! # 零角変更の実四角形ホモトピーの可逆性

概要：左上の中間対象の両端が零頂点なら、変更ホモトピーは全四角形の関手同型。
方針：下側三頂点では定値性、残る頂点では終対象間の射の可逆性を使う。
規約：指定された実ホモトピーを同型の順方向に使う。使われ方：F(0) への零角変更。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial

private lemma fixed_map_vertex_invertible {B K X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ X} (H : SSet.Homotopy F G) (i : B ⟶ K)
    (hi : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      CartesianMonoidalCategory.fst B Δ[1] ≫ i ≫ F) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (i.app (Opposite.op ⦋0⦌) b)).toTruncated := by
  have he := congrArg (fun q : B ⊗ (Δ[1] : SSet.{u}) ⟶ X =>
    q.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) hi
  change H.h.app (Opposite.op ⦋1⦌)
    (i.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
      F.app (Opposite.op ⦋1⦌) (i.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1)) at he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map] at he
  have heq : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (i.app (Opposite.op ⦋0⦌) b)).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X)
        (F.app (Opposite.op ⦋0⦌) (i.app (Opposite.op ⦋0⦌) b))).edge := by
    change H.h.app (Opposite.op ⦋1⦌) (_, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
    exact he
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr heq).mpr
  change IsIso (SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _))
  rw [SSet.Truncated.HomotopyCategory.homMk_id]
  infer_instance

namespace DGModuleSquareData
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {W X Y Y' Z : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}
variable (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData A D W X Y Z) (m : Y ⟶ Y') (r : Y' ⟶ Z) (hr : m ≫ r = s.top)

/-- 零角以外の頂点は定値、零角の辺は終対象間の射なので全成分が可逆。 -/
lemma changeTopMiddleHomotopy_pointwise
    (hs : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 0 1))
    (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (s.changeTopMiddle m r hr).square 0 1))
    (k : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (s.changeTopMiddleHomotopy m r hr) k).toTruncated := by
  have hfix : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
      (s.changeTopMiddleHomotopy m r hr).h =
      CartesianMonoidalCategory.fst Δ[2] Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ s.square := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.changeTopMiddleHomotopy_lower, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_lower]
  rcases k with ⟨a, b⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective a
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective b
  fin_cases i <;> fin_cases j
  · have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{max (u + 1) v} 1).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 3)) =
          (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
      by
        apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro k <;> fin_cases k <;> rfl
    exact (congrArg (fun k : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v}) _⦋0⦌ =>
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
        (s.changeTopMiddleHomotopy m r hr) k).toTruncated) hv).mp
      (fixed_map_vertex_invertible _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1) hfix
        (stdSimplex.obj₀Equiv.symm (0 : Fin 3)))
  · exact isIso_of_isTerminal hs.2.isTerminalHo ht.2.isTerminalHo _
  · have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{max (u + 1) v} 1).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 3)) =
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
      by
        apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro k <;> fin_cases k <;> rfl
    exact (congrArg (fun k : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v}) _⦋0⦌ =>
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
        (s.changeTopMiddleHomotopy m r hr) k).toTruncated) hv).mp
      (fixed_map_vertex_invertible _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1) hfix
        (stdSimplex.obj₀Equiv.symm (1 : Fin 3)))
  · have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{max (u + 1) v} 1).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) =
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
      by
        apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro k <;> fin_cases k <;> rfl
    exact (congrArg (fun k : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v}) _⦋0⦌ =>
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
        (s.changeTopMiddleHomotopy m r hr) k).toTruncated) hv).mp
      (fixed_map_vertex_invertible _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1) hfix
        (stdSimplex.obj₀Equiv.symm (2 : Fin 3)))

/-- 左上の零角を変える実ホモトピーから四角形全体の関手同型を得る。 -/
def changeTopMiddleFunctorIso
    (hs : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 0 1))
    (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (s.changeTopMiddle m r hr).square 0 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso s.square (s.changeTopMiddle m r hr).square :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (s.changeTopMiddleHomotopy m r hr)
    (s.changeTopMiddleHomotopy_pointwise m r hr hs ht)

end DGModuleSquareData
end SerrePositivity.InfinityCategories.Project.DerivedCategories
