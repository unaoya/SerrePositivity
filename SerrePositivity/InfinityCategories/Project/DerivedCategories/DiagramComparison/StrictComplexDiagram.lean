module

public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
概要：ΔとΔᵒᵖに固定したstrict複体図式と、そのobjectwise擬同型を指定する。
方針：本体の複体の通常圏を使い、各評価で擬同型を判定する。
規約：coherent図式のstrict化は結論しない。添字は二つの単体圏だけ。
使われ方：3b-3 R1、HTT 4.2.4.4の加群版の局所化の源。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- 今回の厳密化で許す二つの添字方向。 -/
inductive StrictDiagramDirection
  | simplicial
  | cosimplicial

/-- 方向に応じた元のΔᵒᵖまたはΔ。 -/
def strictDiagramIndex : StrictDiagramDirection → Type
  | .simplicial => SimplexCategoryᵒᵖ
  | .cosimplicial => SimplexCategory

instance strictDiagramIndex_smallCategory (d : StrictDiagramDirection) :
    SmallCategory (strictDiagramIndex d) := by
  cases d <;> dsimp [strictDiagramIndex] <;> infer_instance

/-- 元の複体を値とするstrict単体的または余単体的図式の通常圏。 -/
abbrev StrictComplexDiagram (A : Type u) [CommRing A] (d : StrictDiagramDirection) :=
  strictDiagramIndex d ⥤ SerrePositivity.DifferentialGraded.Complex A

variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)

/-- 各頂点で擬同型となる、元のstrict自然変換の類。 -/
def strictDiagramQuasiIsos : MorphismProperty (StrictComplexDiagram A d) :=
  fun _ _ f => ∀ j, QuasiIso (f.app j)

/-- objectwise擬同型の条件は、同じ各成分の擬同型条件そのもの。 -/
lemma strictDiagramQuasiIsos_iff {X Y : StrictComplexDiagram A d} (f : X ⟶ Y) :
    strictDiagramQuasiIsos A d f ↔ ∀ j, QuasiIso (f.app j) := Iff.rfl

instance strictDiagramQuasiIsos_isMultiplicative : (strictDiagramQuasiIsos A d).IsMultiplicative where
  id_mem X j := by
    change QuasiIso (𝟙 (X.obj j))
    infer_instance
  comp_mem f g hf hg j := by
    haveI := hf j
    haveI := hg j
    change QuasiIso (f.app j ≫ g.app j)
    infer_instance

/-- 元のstrict図式圏のnerve。対象と全自然変換の射列を保持する。 -/
abbrev strictComplexDiagramNerve : SSet.{u + 1} := nerve (StrictComplexDiagram A d)

/-- 元の一単体の唯一の非自明な射がobjectwise擬同型であるという指定辺集合。 -/
def strictDiagramWeakEdges : Set ((strictComplexDiagramNerve A d) _⦋1⦌) :=
  {s | strictDiagramQuasiIsos A d (s.map (homOfLE (show (0 : Fin 2) ≤ 1 by decide)))}

/-- 指定したstrict自然変換のnerve辺は、元の成分が擬同型であるときに限り指定辺。 -/
lemma strictDiagramWeakEdges_mk₁ {X Y : StrictComplexDiagram A d} (f : X ⟶ Y) :
    ComposableArrows.mk₁ f ∈ strictDiagramWeakEdges A d ↔ strictDiagramQuasiIsos A d f := by
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
