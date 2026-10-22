module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightFibrationTotalAssembly
public import SerrePositivity.InfinityCategories.F2.Ind.NerveSublevelLift
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredPosetNerve

/-!
概要：元の weighted 全空間の小さい図式を、同じ下区間上の図式を保って一段で評価する。
方針：全頂点の共通上界で底を厳密に持ち上げ、下区間の終対象で係数を評価する。
規約：元の全空間余極限への射の等号を保持。使われ方：全空間比較の cofinality の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [PartialOrder I] (F : I ⥤ RightFibrationObject C)

/-- 同じ下区間上の weighted 図式を、その指定上界の係数へ評価する。 -/
def weightedTotalBoundedEvaluation (i : I) :
    weightedNerve (sublevelInclusion i ⋙ rightFibrationTotalDiagram F) ⟶ (F.obj i).val.left :=
  weightedNerveTerminalEvaluation (sublevelInclusion i ⋙ rightFibrationTotalDiagram F)
    (isTerminalTop : IsTerminal (⊤ : Set.Iic i))

/-- 同じ上界への評価は、元の全空間余極限への比較を厳密に保つ。 -/
lemma weightedTotalBoundedEvaluation_assembly (i : I) :
    weightedTotalBoundedEvaluation F i ≫ colimit.ι (rightFibrationTotalDiagram F) i =
      weightedNerveBaseMap (sublevelInclusion i) (rightFibrationTotalDiagram F) ≫
        strictRightFibrationTotalAssembly F := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change (colimit.ι (rightFibrationTotalDiagram F) i).app (Opposite.op ⦋n⦌)
      (SSet.yonedaEquiv (s.2.app (Fin.last n) ≫
        (rightFibrationTotalDiagram F).map (homOfLE (s.1.obj (Fin.last n)).property))) =
    SSet.yonedaEquiv (s.2.app (Fin.last n) ≫
      colimit.ι (rightFibrationTotalDiagram F) (s.1.obj (Fin.last n)).val)
  rw [← SSet.yonedaEquiv_comp, Category.assoc, colimit.w]
  rfl

/-- κ-small な元の weighted 図式は一つの下区間へ厳密に持ち上がり、同じ一段で評価できる。 -/
lemma exists_weightedTotal_boundedEvaluation {κ : Cardinal.{u}} [Fact κ.IsRegular]
    [IsCardinalFiltered I κ] {K : SSet.{u}} (hK : IsKappaSmall κ K)
    (a : K ⟶ weightedNerve (rightFibrationTotalDiagram F)) :
    ∃ (i : I) (q : K ⟶ weightedNerve (sublevelInclusion i ⋙ rightFibrationTotalDiagram F)),
      q ≫ weightedNerveBaseMap (sublevelInclusion i) (rightFibrationTotalDiagram F) = a ∧
      (q ≫ weightedTotalBoundedEvaluation F i) ≫ colimit.ι (rightFibrationTotalDiagram F) i =
        a ≫ strictRightFibrationTotalAssembly F := by
  let b := a ≫ weightedNerveProjection (rightFibrationTotalDiagram F)
  have hcard : HasCardinalLT (K _⦋0⦌) κ :=
    (hasCardinalLT_iff_cardinal_mk_lt _ _).mpr (cardinal_vertices_lt_of_isKappaSmall hK)
  obtain ⟨i, ⟨hi⟩⟩ := IsCardinalFiltered.exists_max
    (κ := κ) (fun v : K _⦋0⦌ => (b.app _ v).obj 0) hcard
  let d := nerveSublevelLift b i (fun v => leOfHom (hi v))
  have hd : a ≫ weightedNerveProjection (rightFibrationTotalDiagram F) =
      d ≫ nerveMap (sublevelInclusion i) :=
    (nerveSublevelLift_inclusion b i (fun v => leOfHom (hi v))).symm
  let q := weightedNerveBaseChangeLift (sublevelInclusion i) (rightFibrationTotalDiagram F) a d hd
  have hq := weightedNerveBaseChangeLift_base
    (sublevelInclusion i) (rightFibrationTotalDiagram F) a d hd
  refine ⟨i, q, hq, ?_⟩
  rw [Category.assoc, weightedTotalBoundedEvaluation_assembly, ← Category.assoc, hq]

end SerrePositivity.InfinityCategories.F2.Ind
