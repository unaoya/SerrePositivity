module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientFractionTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ArrowIsoFromCommutingEdges
/-!
概要：商の任意実辺は、元の実辺の像と区間上の全関手圏で同型。
方針：指定辺の実分数三角形を、可逆分母と恒等終点を持つ実可換正方形に読む。
規約：H⁰ の Arrow の同型だけでは済ませない。使われ方：商からの関手の完全性の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
/-- 指定商対象を両端とする実辺は、元の同じ分数三角形の分子の像と全関手圏で同型。 -/
lemma dgQuotientEdge_exists_original_arrow_iso (P : Set D)
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) {x y : D}
    (k : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj y))) :
    ∃ b : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) _⦋1⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.yonedaEquiv.symm b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
        (SSet.yonedaEquiv.symm k.edge)) := by
  obtain ⟨z, d, g, _, hd, ⟨t⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientEdge_exists_fractionTriangle A D P hP k
  let idY := Truncated.Edge.id (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj y))
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P) idY := by
    change IsIso (Truncated.HomotopyCategory.homMk idY)
    rw [Truncated.HomotopyCategory.homMk_id]
    infer_instance
  have hc : Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedMappedEdge A D (DGQuotient.QuotientObject D P) (DGQuotient.inclusion A D P) g) ≫
      Truncated.HomotopyCategory.homMk idY =
        Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedMappedEdge A D (DGQuotient.QuotientObject D P)
            (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P) d) ≫ Truncated.HomotopyCategory.homMk k := by
    have hid : Truncated.HomotopyCategory.homMk idY = 𝟙 _ :=
      by
        dsimp only [idY]
        exact Truncated.HomotopyCategory.homMk_id _
    exact ((congrArg (fun v => Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedMappedEdge A D (DGQuotient.QuotientObject D P)
        (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P) g) ≫ v) hid).trans (Category.comp_id _)).trans
          (Truncated.HomotopyCategory.homMk_comp_homMk t).symm
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.nonempty_arrowFunctorIso_of_comm _ k _ idY hd hi hc
  refine ⟨g.edge, ?_⟩
  rw [SSet.yonedaEquiv_symm_comp]
  exact ⟨e⟩
/-- 商の任意の実一次単体は、元の実一次単体の像と区間上の全関手圏で同型。 -/
lemma dgQuotientNerveProjection_arrow_lifts (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P) _⦋1⦌) :
    ∃ b : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) _⦋1⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.yonedaEquiv.symm b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
        (SSet.yonedaEquiv.symm a)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a
  let x := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (DGQuotient.QuotientObject D P)) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P).δ 1 a)
  let y := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (DGQuotient.QuotientObject D P)) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P).δ 0 a)
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P).δ 1 a :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A _).symm_apply_apply _
  have hy : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P).δ 0 a :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A _).symm_apply_apply _
  let k : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x.val))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj y.val)) := {
    edge := a
    src_eq := hx.symm
    tgt_eq := hy.symm }
  exact dgQuotientEdge_exists_original_arrow_iso A D P hP k
end SerrePositivity.InfinityCategories.Project.DerivedCategories
