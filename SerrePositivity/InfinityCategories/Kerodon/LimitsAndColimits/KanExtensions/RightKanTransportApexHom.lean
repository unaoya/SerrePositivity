module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanTransportApex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ConeApexEvaluationVertex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero

/-!
概要：指定右Kan輸送の頂点射は、元の頂点等式の射と一致する。
方針：元の同じ定値辺をホモトピー圏で評価し、両端の等式による移送を表示する。
規約：HTT §4.3.2、Kerodon §7.3（Tag 02Y1）の既存輸送の計算法則。
使われ方：S8 の指定余単位を保つ比較の頂点で、大きい定義の展開を避ける。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

private lemma constantEdge_hom {X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) x y) (hx : x = z) (hy : y = z)
    (h : e.edge = PinchedHom.constant z 1) :
    Truncated.HomotopyCategory.homMk e ≫ eqToHom (congrArg (fun v => (HomotopyCategory.mk v : hoFunctor.obj X)) hy) =
      eqToHom (congrArg (fun v => (HomotopyCategory.mk v : hoFunctor.obj X)) hx) := by
  subst x y
  have he : e = Truncated.Edge.id (X := (truncation 2).obj X) z := by
    apply Truncated.Edge.ext
    exact h.trans (pinchedConstant_one z)
  rw [he]
  simpa only [eqToHom_refl, Category.comp_id, SSet.HomotopyCategory.mk] using
    (Truncated.HomotopyCategory.homMk_id (V := (truncation 2).obj X) z)

/-- 指定輸送の頂点の射は、同じ元の頂点等式だけの射になる。 -/
lemma RightKanConeTransport.apex_hom
    {K C D : SSet.{u}} {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} {c : C _⦋0⦌}
    (t : RightKanConeTransport δ F₀ F α c) :
    (hoFunctor.map (coneApexEvaluation (rightKanShape δ c) D)).toFunctor.map
      (Truncated.HomotopyCategory.homMk t.edge) ≫
        eqToHom (congrArg (fun v => (HomotopyCategory.mk v : hoFunctor.obj D))
          ((coneApexEvaluation_vertex t.cone).trans t.cone_vertex)) =
      eqToHom (congrArg (fun v => (HomotopyCategory.mk v : hoFunctor.obj D))
        ((coneApexEvaluation_vertex (rightKanCanonicalCone δ F c)).trans
          (rightKanCanonicalCone_vertex δ F c))) := by
  let e := t.edge.map ((truncation 2).map (coneApexEvaluation (rightKanShape δ c) D))
  have hx : (coneApexEvaluation (rightKanShape δ c) D).app _
      (SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
        (rightKanCanonicalCone δ F c).val) = (rightKanCanonicalCone δ F c).vertex :=
    coneApexEvaluation_vertex (rightKanCanonicalCone δ F c)
  have hy := (coneApexEvaluation_vertex t.cone).trans
    (t.cone_vertex.trans (rightKanCanonicalCone_vertex δ F c).symm)
  have h := constantEdge_hom e hx hy t.apex_edge_eq_constant
  change Truncated.HomotopyCategory.homMk e ≫ _ = _
  calc
    _ = (Truncated.HomotopyCategory.homMk e ≫
        eqToHom (congrArg (fun v => (HomotopyCategory.mk v : hoFunctor.obj D)) hy)) ≫
          eqToHom (congrArg (fun v => (HomotopyCategory.mk v : hoFunctor.obj D)) (rightKanCanonicalCone_vertex δ F c)) := by
      simp only [Category.assoc, eqToHom_trans]
    _ = _ := by rw [h]; simp only [eqToHom_trans]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
