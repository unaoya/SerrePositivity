module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronModel
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberShortComplex

/-! # 任意の二射の八面体模型

概要：安定 quasicategory のホモトピー圏の任意の合成可能な二射は八面体模型を持つ。
方針：二射を辺で表し、合成二単体と第一射の cofiber 四角形から二長方形を作る。
規約：模型の第一・第二辺は元の射と端点を含めて等しい。使われ方：TR4 の全二射への適用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Pretriangulated Triangulated MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：合成可能な二辺を短辺に持つ実際の二単体が存在する。
方針：二切断 quasicategory の合成構造を Yoneda で単体的な射へ移す。
規約：二つの短辺は単体的な射として厳密に指定。使われ方：八面体の底辺二単体。 -/
lemma exists_compositionSimplex {X : SSet.{u}} [Quasicategory X] {x y z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj X) y z) :
    ∃ τ : (Δ[2] : SSet.{u}) ⟶ X,
      stdSimplex.δ (2 : Fin 3) ≫ τ = SSet.yonedaEquiv.symm f.edge ∧
      stdSimplex.δ (0 : Fin 3) ≫ τ = SSet.yonedaEquiv.symm g.edge := by
  let c := SSet.Truncated.Edge.compStruct f g
  refine ⟨SSet.yonedaEquiv.symm c.simplex, ?_, ?_⟩
  · apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (fun a => X.δ 2 a) (SSet.yonedaEquiv.apply_symm_apply c.simplex)).trans
      (c.d₂.trans (SSet.yonedaEquiv.apply_symm_apply f.edge).symm)
  · apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (fun a => X.δ 0 a) (SSet.yonedaEquiv.apply_symm_apply c.simplex)).trans
      (c.d₀.trans (SSet.yonedaEquiv.apply_symm_apply g.edge).symm)

/-- 概要：ホモトピー圏の任意の合成可能な二射は八面体模型を持つ。
方針：辺の代表と第一辺の cofiber を選び、二長方形の模型の第一・第二辺を元の射へ戻す。
規約：対象の表示も含む Arrow の等号を使い、三角形の選択を前提にしない。
使われ方：八面体公理の IsTriangulated instance。 -/
lemma octahedronModel_of_morphisms {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {A B D : hoFunctor.obj X} (f : A ⟶ B) (g : B ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.OctahedronModel (Arrow.mk f) (Arrow.mk g) := by
  obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective A
  obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective B
  obtain ⟨z, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective D
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y f
  obtain ⟨q, hq⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective y z g
  obtain ⟨τ, hτ₂, hτ₀⟩ := exists_compositionSimplex e q
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare e
  have hfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ s.toZeroTriangle.square = stdSimplex.δ (2 : Fin 3) ≫ τ :=
    s.bottom_edge.trans hτ₂.symm
  obtain ⟨d⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.nonempty_cofiberOctahedronDiagram s.toZeroTriangle s.isPushout τ hfirst
  have hm := d.octahedronModel s.isPushout
  have hf : Arrow.mk s.toZeroTriangle.hoShortComplex.f = Arrow.mk f :=
    s.hoShortComplex_f_arrow.trans (congrArg Arrow.mk he)
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ d.second.outerZeroTriangle.square =
      SSet.yonedaEquiv.symm q.edge := by
    rw [d.next_firstEdge, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_bottomEdge, d.first.bottom_eq]
    exact hτ₀
  have hg' : Arrow.mk d.second.outerZeroTriangle.hoShortComplex.f =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk q) := by
    apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow_edge, hb]
    exact SSet.yonedaEquiv.apply_symm_apply q.edge
  have hg := hg'.trans (congrArg Arrow.mk hq)
  rw [hf, hg] at hm
  exact hm

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
