module

public import SerrePositivity.InfinityCategories.Core.SliceLaxMap

/-!
概要：直接定義の slice と太い slice の同値。
方針：任意のパラメーターで関手の同型類を比較し、逆関手を選んで二つの逆合成を同定する。
規約：値域 X は quasicategory、添字 K は任意。
使われ方：Kerodon Proposition 4.6.4.19。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：太い slice への任意の関手は、slice からの比較を通る関手と同型。
方針：固定図式上の fat join 比較の逆で頂点を戻し、二つの普遍性と同型判定を使う。
規約：パラメーター A は任意、X は quasicategory。
使われ方：Kerodon Proposition 4.6.4.19 の同型類の全射性。 -/
lemma exists_functorIso_comp_sliceLaxMap {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (A : SSet.{u}) (a : A ⟶ laxSlice p) :
    ∃ f : A ⟶ sliceOver p, Nonempty (FunctorIso (f ≫ sliceLaxMap p) a) := by
  let q := fixedDiagramPre (joinInr A K) (fatJoinInr A K) (fatJoinComparison A K)
    (fatJoinInr_comparison A K) p
  have he : IsQCatEquivalence q := isQCatEquivalence_fixedDiagramPre
    (joinInr A K) (fatJoinInr A K) (fatJoinComparison A K) (fatJoinInr_comparison A K) p
    (isPrecompositionEquivalence_fatJoinComparison A K)
  let e := he.choose
  let y := laxSliceFixedDiagramVertex a
  let v := e.inv.app (Opposite.op ⦋0⦌) y
  let f := (sliceOverFixedDiagramVertexEquiv p A).symm v
  have hv : sliceOverFixedDiagramVertex f = v :=
    (sliceOverFixedDiagramVertexEquiv p A).apply_symm_apply v
  have hq : q.app (Opposite.op ⦋0⦌) v = laxSliceFixedDiagramVertex (f ≫ sliceLaxMap p) := by
    rw [← hv]
    exact sliceLaxMap_fixedDiagramVertex f
  have et := FunctorIso.app e.invHomIso y
  change VertexIso (X := vertexFiber ((pre (fatJoinInr A K)).app X) (functorVertex p))
    (q.app (Opposite.op ⦋0⦌) v) y at et
  refine ⟨f, ?_⟩
  apply nonempty_functorIso_of_laxSliceFixedDiagramVertexIso
  exact (eqToIso (congrArg SSet.HomotopyCategory.mk hq)).symm ≪≫ et

/-- 概要：直接定義の slice から太い slice への比較は quasicategory の同値。
方針：恒等関手の同型類の逆像から逆関手を選び、同型の反映で他方の逆合成を同定する。
規約：X は quasicategory、K は任意、追加の有限性・非空性は不要。
使われ方：Kerodon Proposition 4.6.4.19 の太い slice の比較。 -/
lemma isQCatEquivalence_sliceLaxMap {K X : SSet.{u}} [Quasicategory X] (p : K ⟶ X) :
    IsQCatEquivalence (sliceLaxMap p) := by
  obtain ⟨g, ⟨eg⟩⟩ := exists_functorIso_comp_sliceLaxMap p (laxSlice p) (𝟙 (laxSlice p))
  have ep : FunctorIso ((sliceLaxMap p ≫ g) ≫ sliceLaxMap p)
      ((𝟙 (sliceOver p)) ≫ sliceLaxMap p) := by
    have et := FunctorIso.precomp eg (sliceLaxMap p)
    simpa only [Category.assoc, Category.comp_id, Category.id_comp] using et
  have eu := nonempty_functorIso_of_sliceLaxMap (sliceLaxMap p ≫ g) (𝟙 (sliceOver p)) ep
  exact ⟨g, eu, ⟨eg⟩⟩

end SerrePositivity.InfinityCategories
