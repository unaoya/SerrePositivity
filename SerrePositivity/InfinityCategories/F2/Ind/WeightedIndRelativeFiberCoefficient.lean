module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndRelativeCoefficientColimit
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndDensityFiber
public import SerrePositivity.InfinityCategories.F2.Ind.RelativeJoinFiberVertex
public import SerrePositivity.InfinityCategories.F2.Ind.NativeCoconePreservationTransport

/-!
概要：元の相対 join の実際の fiber 余錐を、同じ weighted fiber 同型で元の係数へ戻す。
方針：同じ全図式の厳密な左制限と元の係数包含を使い、図式と指定頂点を正規化する。
規約：実際の fiber 余錐そのもの。使われ方：元の全単位の局所余極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [PartialOrder I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I)

/-- 元の weighted fiber と同じ係数全空間の、元の持ち上げた同型。 -/
abbrev weightedIndCoefficientFiberIso :=
  uliftWeightedNerveFiberIso.{u, u + 1} (rightFibrationTotalDiagram F) i
local notation "p" => weightedIndDensityIndexProjection F
local notation "v" => ULift.up (nerveVertex i)
local notation "e" => weightedIndCoefficientFiberIso F i
local notation "H" => weightedIndDensityRelativeDiagram κ F hF
local notation "D" => weightedIndCoefficientDiagram κ F i
local notation "z" => weightedIndCoefficientVertex κ F hF i

/-- 同じ全図式の実際の fiber 図式は、元の係数同型で元の係数図式を厳密に回収する。 -/
lemma weightedIndRelativeFiberCoefficient_diagram :
    (e).hom ≫ (vertexFiberι p v ≫ relativeJoinInl p (𝟙 _) ≫ H) = D := by
  rw [weightedIndDensityRelativeDiagram_left, ← Category.assoc,
    uliftWeightedIndDensityFiberIso_ι F i, weightedIndDensitySource,
    ← Category.assoc, ← CategoryTheory.Functor.map_comp, weightedDensityProjection_coefficient]

/-- 実際の相対 join fiber 余錐を元の同じ係数全空間へ戻した、元の係数図式上の余錐。 -/
def weightedIndRelativeFiberCoefficientCocone : JoinCocone D :=
  coherentCoconeOfDiagramEq (weightedIndRelativeFiberCoefficient_diagram κ F hF i)
    ((F1B.kanRelativeJoinFiberCocone p v H).restrict (e).hom)

/-- 同じ実際の fiber 余錐の頂点は、元の共同分類の同じ指定係数頂点。 -/
lemma weightedIndRelativeFiberCoefficientCocone_vertex :
    (weightedIndRelativeFiberCoefficientCocone κ F hF i).vertex = z := by
  rw [weightedIndRelativeFiberCoefficientCocone, coherentCoconeOfDiagramEq_vertex,
    JoinCocone.vertex_restrict, relativeJoinFiberCocone_vertex,
    weightedIndDensityRelativeDiagram_right]

/-- 同じ実際の fiber 余錐の全写像は、元の fiber 同型・元の包含・元の全図式の同じ合成。 -/
lemma weightedIndRelativeFiberCoefficientCocone_val :
    (weightedIndRelativeFiberCoefficientCocone κ F hF i).val =
      joinMap (e).hom (𝟙 (Δ[0] : SSet.{u + 1})) ≫ relativeJoinFiberEmbedding p v ≫ H := by
  rw [weightedIndRelativeFiberCoefficientCocone, coherentCoconeOfDiagramEq_val]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
