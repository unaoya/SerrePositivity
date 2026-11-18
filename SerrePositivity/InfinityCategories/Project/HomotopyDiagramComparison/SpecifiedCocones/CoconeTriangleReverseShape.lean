module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SquareOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinSimplexInclusions
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinPrismFixed
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone

/-!
概要：錐の辺に沿う全三角形を反転し、余錐の同じ三角形として表示する形状の法則。
方針：標準二単体の有限な反転を確認し、join の逆反転の自然性で一般の辺へ移す。
規約：頂点だけでなく二単体全体の射の等式。
使われ方：HTT 4.2.4.1、Kerodon §4.6.7（Tag 01LA）、S8 の元の押し出し四角形。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 辺と点の三角形の標準反転は、点と辺の三角形の反対に等しい。
HTT 4.2.4.1、Kerodon §4.6.7（Tag 01LA）、固定した有限形状の計算則。 -/
lemma coconeTriangleReverseShape_standard :
    (joinStdSimplexIso 1 0).inv ≫
        joinMap (stdSimplex.opIso ⦋1⦌).inv (stdSimplex.opIso ⦋0⦌).inv ≫
        (stableJoinReverseIso (Δ[0] : SSet.{u}) Δ[1]).inv =
      (stdSimplex.opIso ⦋2⦌).inv ≫ SSet.opFunctor.map (pointJoinStdSimplexIso 1).inv := by
  let eL : (join (Δ[0] : SSet.{u}) Δ[1]).op ≅ Δ[2] :=
    stableJoinReverseIso Δ[0] Δ[1] ≪≫
      joinIso (stdSimplex.opIso ⦋1⦌) (stdSimplex.opIso ⦋0⦌) ≪≫ joinStdSimplexIso 1 0
  let eR : (join (Δ[0] : SSet.{u}) Δ[1]).op ≅ Δ[2] :=
    SSet.opFunctor.mapIso (pointJoinStdSimplexIso 1) ≪≫ stdSimplex.opIso ⦋2⦌
  have h : eL.hom = eR.hom := by
    apply hom_to_stdSimplex_ext_vertices
    intro x
    obtain ⟨s, rfl⟩ := SSet.opObjEquiv.symm.surjective x
    obtain ⟨a, rfl⟩ | ⟨b, rfl⟩ := join_vertex_cases (Δ[0] : SSet.{u}) Δ[1] s
    · have ha : a = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
        apply stdSimplex.ext
        intro i
        apply Fin.ext
        have h₁ : (a i).val < 1 := (a i).isLt
        have h₂ : ((SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) i).val < 1 :=
          ((SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) i).isLt
        omega
      subst a
      apply stdSimplex.ext
      intro i
      fin_cases i
      rfl
    · have hb : b = stdSimplex.objMk (OrderHom.const (Fin 1) (b 0)) := by
        apply stdSimplex.ext
        intro i
        fin_cases i
        rfl
      rw [hb]
      generalize b 0 = k
      fin_cases k
      all_goals apply stdSimplex.ext
      all_goals intro i
      all_goals fin_cases i
      all_goals rfl
  have he : eL = eR := Iso.ext h
  have hi := congrArg Iso.inv he
  simpa only [eL, eR, Iso.trans_inv, CategoryTheory.Functor.mapIso_inv, joinIso, Category.assoc] using hi

/-- 錐の同じ辺の全三角形を反転すると、余錐の三角形の反対が得られる。
HTT 4.2.4.1、Kerodon §4.6.7（Tag 01LA）。図式・係数に充填性を課さない。 -/
lemma reverseCocone_triangle_val {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (a : (Δ[1] : SSet.{u}) ⟶ K) :
    ((joinStdSimplexIso 1 0).inv ≫
      joinMap ((stdSimplex.opIso ⦋1⦌).inv ≫ SSet.opFunctor.map a) (𝟙 Δ[0])) ≫
        c.reverseCocone.val =
    (stdSimplex.opIso ⦋2⦌).inv ≫ SSet.opFunctor.map
      ((pointJoinStdSimplexIso 1).inv ≫ joinMap (𝟙 Δ[0]) a ≫ c.val) := by
  rw [SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.JoinCone.reverseCocone_val]
  have hj : joinMap ((stdSimplex.opIso ⦋1⦌).inv ≫ SSet.opFunctor.map a) (𝟙 Δ[0]) ≫
      joinMap (𝟙 K.op) (stdSimplex.opIso ⦋0⦌).inv =
    joinMap (stdSimplex.opIso ⦋1⦌).inv (stdSimplex.opIso ⦋0⦌).inv ≫
      joinMap (SSet.opFunctor.map a) (𝟙 (Δ[0] : SSet.{u}).op) := by
    simp only [← joinMap_comp, Category.comp_id, Category.id_comp]
  have hn := stableJoinReverse_inv_naturality (𝟙 (Δ[0] : SSet.{u})) a
  rw [CategoryTheory.Functor.map_id] at hn
  calc
    _ = (joinStdSimplexIso 1 0).inv ≫
        (joinMap ((stdSimplex.opIso ⦋1⦌).inv ≫ SSet.opFunctor.map a) (𝟙 Δ[0]) ≫
          joinMap (𝟙 K.op) (stdSimplex.opIso ⦋0⦌).inv) ≫
        (stableJoinReverseIso Δ[0] K).inv ≫ SSet.opFunctor.map c.val := by
      simp only [Category.assoc]
    _ = (joinStdSimplexIso 1 0).inv ≫
        joinMap (stdSimplex.opIso ⦋1⦌).inv (stdSimplex.opIso ⦋0⦌).inv ≫
        (joinMap (SSet.opFunctor.map a) (𝟙 (Δ[0] : SSet.{u}).op) ≫
          (stableJoinReverseIso Δ[0] K).inv) ≫ SSet.opFunctor.map c.val := by
      rw [hj]
      simp only [Category.assoc]
    _ = _ := by
      rw [hn]
      have hstd : ((joinStdSimplexIso 1 0).inv ≫
          joinMap (stdSimplex.opIso ⦋1⦌).inv (stdSimplex.opIso ⦋0⦌).inv) ≫
          (stableJoinReverseIso (Δ[0] : SSet.{u}) Δ[1]).inv =
        (stdSimplex.opIso ⦋2⦌).inv ≫
          SSet.opFunctor.map (pointJoinStdSimplexIso 1).inv := by
        simpa only [Category.assoc] using (coconeTriangleReverseShape_standard.{u})
      simp only [← Category.assoc]
      rw [hstd]
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
