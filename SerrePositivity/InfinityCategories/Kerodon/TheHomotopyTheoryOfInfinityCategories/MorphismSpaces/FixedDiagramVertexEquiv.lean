module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SliceFixedDiagramIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LaxSliceFixedDiagramIso

/-!
概要：図式を固定する関手と固定図式上の fiber の頂点の同値。
方針：内部 Hom の関手頂点の同値を固定条件に制限する。
規約：零単体の厳密な対応を扱う。
使われ方：Kerodon §4.6.4（Tag 01KE） の関手の同型類の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：固定図式を延長する関手と対応する fiber の頂点は同値。
方針：関手頂点の同値を可換条件に制限する。
規約：quasicategory 性・単射性は不要。
使われ方：Kerodon §4.6.4（Tag 01KE） の固定図式上の対象の表示。 -/
def fixedDiagramVertexEquiv {K T X : SSet.{u}} (j : K ⟶ T) (p : K ⟶ X) :
    {F : T ⟶ X // j ≫ F = p} ≃ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre j).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) _⦋0⦌ where
  toFun F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramVertex j p F.val F.property
  invFun v :=
    let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv T X).symm v.val
    ⟨F, by
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
      have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = v.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv T X).apply_symm_apply v.val
      have hv : ((pre j).app X).app (Opposite.op ⦋0⦌) v.val = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p :=
        v.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _)
      calc
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ F) = ((pre j).app X).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) := rfl
        _ = ((pre j).app X).app (Opposite.op ⦋0⦌) v.val := congrArg _ hF
        _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p := hv⟩
  left_inv F := by
    apply Subtype.ext
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv T X).symm_apply_apply F.val
  right_inv v := by
    apply Subtype.ext
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv T X).apply_symm_apply v.val

/-- 概要：slice への射は固定図式上の join の関手の頂点と同値。
方針：slice の普遍性と固定関手の頂点の表示を合成する。
規約：任意のパラメーターを扱う。
使われ方：Kerodon §4.6.4（Tag 01KE） の同型類の全射性。 -/
def sliceOverFixedDiagramVertexEquiv {K X : SSet.{u}} (p : K ⟶ X) (A : SSet.{u}) :
    (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) ≃ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K)).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverEquiv p).trans (fixedDiagramVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K) p)

/-- 概要：太い slice への射は固定図式上の太い join の関手の頂点と同値。
方針：太い slice の普遍性と固定関手の頂点の表示を合成する。
規約：任意のパラメーターを扱う。
使われ方：Kerodon §4.6.4（Tag 01KE） の同型類の比較。 -/
noncomputable def laxSliceFixedDiagramVertexEquiv {K X : SSet.{u}} (p : K ⟶ X) (A : SSet.{u}) :
    (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSlice p) ≃ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K)).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceHomEquiv p A).trans (fixedDiagramVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K) p)

/-- 概要：quasicategory の同値は二頂点の同型を反映する。
方針：逆射で同型を戻し、単位の同型で両端を元に戻す。
規約：同値の構造の選択は結論の存在にのみ使う。
使われ方：Kerodon §4.6.4（Tag 01KE） の固定図式の比較による同型の反映。 -/
lemma IsQCatEquivalence.vertexIso_of_map {E F : SSet.{u}}
    [Quasicategory E] [Quasicategory F] {f : E ⟶ F} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f)
    {x y : E _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := F)
      (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) := by
  let a := hf.choose
  exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app a.homInvIso x).symm ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e a.inv ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app a.homInvIso y⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsQCatEquivalence (vertexIso_of_map)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
