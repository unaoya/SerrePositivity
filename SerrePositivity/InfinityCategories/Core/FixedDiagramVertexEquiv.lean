module

public import SerrePositivity.InfinityCategories.Core.SliceFixedDiagramIso
public import SerrePositivity.InfinityCategories.Core.LaxSliceFixedDiagramIso

/-!
概要：図式を固定する関手と固定図式上の fiber の頂点の同値。
方針：内部 Hom の関手頂点の同値を固定条件に制限する。
規約：零単体の厳密な対応を扱う。
使われ方：Kerodon §4.6.4 の関手の同型類の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：固定図式を延長する関手と対応する fiber の頂点は同値。
方針：関手頂点の同値を可換条件に制限する。
規約：quasicategory 性・単射性は不要。
使われ方：Kerodon §4.6.4 の固定図式上の対象の表示。 -/
def fixedDiagramVertexEquiv {K T X : SSet.{u}} (j : K ⟶ T) (p : K ⟶ X) :
    {F : T ⟶ X // j ≫ F = p} ≃ (vertexFiber ((pre j).app X) (functorVertex p)) _⦋0⦌ where
  toFun F := fixedDiagramVertex j p F.val F.property
  invFun v :=
    let F := (functorVertexEquiv T X).symm v.val
    ⟨F, by
      apply functorVertex_injective
      have hF : functorVertex F = v.val := (functorVertexEquiv T X).apply_symm_apply v.val
      have hv : ((pre j).app X).app (Opposite.op ⦋0⦌) v.val = functorVertex p :=
        v.property.trans (pinchedConstant_zero _)
      calc
        functorVertex (j ≫ F) = ((pre j).app X).app (Opposite.op ⦋0⦌) (functorVertex F) := rfl
        _ = ((pre j).app X).app (Opposite.op ⦋0⦌) v.val := congrArg _ hF
        _ = functorVertex p := hv⟩
  left_inv F := by
    apply Subtype.ext
    exact (functorVertexEquiv T X).symm_apply_apply F.val
  right_inv v := by
    apply Subtype.ext
    exact (functorVertexEquiv T X).apply_symm_apply v.val

/-- 概要：slice への射は固定図式上の join の関手の頂点と同値。
方針：slice の普遍性と固定関手の頂点の表示を合成する。
規約：任意のパラメーターを扱う。
使われ方：Kerodon §4.6.4 の同型類の全射性。 -/
def sliceOverFixedDiagramVertexEquiv {K X : SSet.{u}} (p : K ⟶ X) (A : SSet.{u}) :
    (A ⟶ sliceOver p) ≃ (vertexFiber ((pre (joinInr A K)).app X) (functorVertex p)) _⦋0⦌ :=
  (sliceOverEquiv p).trans (fixedDiagramVertexEquiv (joinInr A K) p)

/-- 概要：太い slice への射は固定図式上の太い join の関手の頂点と同値。
方針：太い slice の普遍性と固定関手の頂点の表示を合成する。
規約：任意のパラメーターを扱う。
使われ方：Kerodon §4.6.4 の同型類の比較。 -/
noncomputable def laxSliceFixedDiagramVertexEquiv {K X : SSet.{u}} (p : K ⟶ X) (A : SSet.{u}) :
    (A ⟶ laxSlice p) ≃ (vertexFiber ((pre (fatJoinInr A K)).app X) (functorVertex p)) _⦋0⦌ :=
  (laxSliceHomEquiv p A).trans (fixedDiagramVertexEquiv (fatJoinInr A K) p)

/-- 概要：quasicategory の同値は二頂点の同型を反映する。
方針：逆射で同型を戻し、単位の同型で両端を元に戻す。
規約：同値の構造の選択は結論の存在にのみ使う。
使われ方：Kerodon §4.6.4 の固定図式の比較による同型の反映。 -/
lemma IsQCatEquivalence.vertexIso_of_map {E F : SSet.{u}}
    [Quasicategory E] [Quasicategory F] {f : E ⟶ F} (hf : IsQCatEquivalence f)
    {x y : E _⦋0⦌} (e : VertexIso (X := F)
      (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)) : Nonempty (VertexIso x y) := by
  let a := hf.choose
  exact ⟨(FunctorIso.app a.homInvIso x).symm ≪≫ VertexIso.map e a.inv ≪≫
    FunctorIso.app a.homInvIso y⟩

end SerrePositivity.InfinityCategories
