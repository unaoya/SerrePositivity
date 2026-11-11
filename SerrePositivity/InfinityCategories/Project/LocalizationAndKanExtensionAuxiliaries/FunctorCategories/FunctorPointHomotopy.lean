module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorDiagramPath
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber

/-!
概要：関手の零単体表示の間のホモトピーを、元の図式のホモトピーへ戻す。
方針：零単体で時間辺を評価して uncurry し、部分図式の固定条件を保持する。
規約：零単体表示の同型や Hom の類から別の辺を選び直さない。
使われ方：B1 の相対 path 写像から得た輸送の比較を図式へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：関手の零単体表示を零頂点で評価すると元の関手頂点。
方針：零単体上の Yoneda の逆射は定値射であることを使う。
規約：頂点の厳密な等式。
使われ方：関手の零単体表示のホモトピーの端点の回収。 -/
lemma functorDiagramPointEquiv_vertex {B X : SSet.{u}} (f : B ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorDiagramPointEquiv B X f).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f := by
  change (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)).app _ _ = _
  rw [SSet.yonedaEquiv_symm_zero]
  rfl

/-- 概要：零単体表示の間の基底固定ホモトピーから、元の相対図式ホモトピーを得る。
方針：唯一の零頂点で時間辺を取り出し、前合成の像の恒等性を uncurry する。
規約：指定したホモトピーの代表を保持し、比較の辺を再選択しない。
使われ方：相対 path 写像の持ち上げの比較を元の図式へ戻す。 -/
lemma exists_relativeFunctorPointHomotopy {A B X : SSet.{u}} (i : A ⟶ B)
    {f g : B ⟶ X}
    (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorDiagramPointEquiv B X f) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorDiagramPointEquiv B X g))
    (hH : H.h ≫ (pre i).app X = fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorDiagramPointEquiv A X (i ≫ g)) :
    ∃ D : SSet.Homotopy f g,
      (i ▷ (Δ[1] : SSet.{u})) ≫ D.h = fst A (Δ[1] : SSet.{u}) ≫ i ≫ g := by
  let v := stdSimplex.obj₀Equiv.symm (0 : Fin 1)
  let k := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H v).toTruncated
  let k' : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g) :=
    ⟨k.edge, k.src_eq.trans (functorDiagramPointEquiv_vertex f),
      k.tgt_eq.trans (functorDiagramPointEquiv_vertex g)⟩
  have hk : ((pre i).app X).app (Opposite.op ⦋1⦌) k'.edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj X))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ g))).edge := by
    have hh := congrArg
      (fun t : (Δ[0] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom A).obj X ↦
        t.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) hH
    change ((pre i).app X).app (Opposite.op ⦋1⦌)
      (H.h.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) =
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorDiagramPointEquiv A X (i ≫ g)).app (Opposite.op ⦋1⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1) at hh
    have hr : (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorDiagramPointEquiv A X (i ≫ g)).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ g)) 1 := by
      change (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ g))).app _ _ = _
      rw [SSet.yonedaEquiv_symm_zero]
      rfl
    have hh' := hh.trans hr
    change ((pre i).app X).app (Opposite.op ⦋1⦌)
      (H.h.app (Opposite.op ⦋1⦌)
        ((SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[0] : SSet.{u})) v).edge,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) = _
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one] using hh'
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge k', ?_⟩
  change (i ▷ (Δ[1] : SSet.{u})) ≫ uncurry (SSet.yonedaEquiv.symm k'.edge) = _
  rw [← uncurry_pre_app, SSet.yonedaEquiv_symm_comp, hk]
  have hc : SSet.yonedaEquiv.symm
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj X))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ g))).edge =
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ g)) : (Δ[1] : SSet.{u}) ⟶ (ihom A).obj X) := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ g))).symm
  rw [hc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
