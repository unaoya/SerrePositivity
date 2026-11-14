module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeCoherentCone
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits

/-!
概要：同じ Tot の指定 coherent 錐を、既存比較で実 dg nerve の錐へ送る。
方針：全 join 錐を比較射で後合成し、元の頂点の計算式を使う。
規約：錐・頂点を選び直さず、普遍性は別工程で示す。
使われ方：HA 1.2.4、G10 の元の Tot の錐から導来圏への移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- coherent 錐の頂点は、元の Tot の指定頂点に等しい。 -/
theorem nativeCoherentCone_vertex (X : CosimplicialObject (Complex A)) :
    (nativeCoherentCone X).vertex = coherentNerveVertex
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)) := by
  rw [JoinCone.vertex_eq, nativeCoherentCone_vertexMap, Equiv.apply_symm_apply]

/-- 元の strict 余単体図式の、同じ比較で得る dg nerve の図式。 -/
def nativeDGDiagram (X : CosimplicialObject (Complex A)) :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ⟶
      dgNerve A (Complex A) :=
  strictCoherentDiagram (liftedClosedDiagram X) ≫ coherentComparison (R := A) (D := Complex A)

/-- 元の Tot を頂点とする、同じ全高次単体の dg nerve の join 錐。 -/
def nativeDGCone (X : CosimplicialObject (Complex A)) : JoinCone (nativeDGDiagram X) :=
  mapJoinCone (coherentComparison (R := A) (D := Complex A)) (nativeCoherentCone X)

/-- dg nerve へ移した錐も、元の積 Tot の頂点を厳密に保つ。 -/
theorem nativeDGCone_vertex (X : CosimplicialObject (Complex A)) :
    (nativeDGCone X).vertex = Simplex.vertex ((productTotalFunctor A).obj X) := by
  rw [nativeDGCone, mapJoinCone_vertex, nativeCoherentCone_vertex,
    coherentNerveVertex_eq_vertex, coherentComparison_vertex]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
