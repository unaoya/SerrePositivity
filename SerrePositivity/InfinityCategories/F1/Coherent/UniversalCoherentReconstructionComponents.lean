module

public import SerrePositivity.InfinityCategories.F1.Coherent.StraighteningFamilyRestriction
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorFamilyVertices

/-!
概要：普遍族の再構成の各成分を個別に選んだ分類図式と結ぶ。
方針：普遍図式を指定頂点で制限し同じ全空間上の二表現を比較する。
規約：普遍族の射の実際の零単体での値を対象とする。
使われ方：族全体の比較と選択した単位・余単位の成分の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：族の頂点で制限した図式の関手頂点は族の実際の頂点の値。
方針：uncurry の頂点公式を関手頂点の全単射で戻す。
規約：パラメーターも図式の始域も任意。
使われ方：普遍再構成の各成分を図式として回収する。 -/
lemma functorVertex_uncurry_at_vertex {A L X : SSet.{u}}
    (t : L ⟶ (ihom A).obj X) (x : L _⦋0⦌) :
    functorVertex (lift (𝟙 A) (SSet.const x) ≫ uncurry t) = t.app _ x := by
  rw [uncurry_at_vertex]
  exact (functorVertexEquiv A X).apply_symm_apply _

/-- 概要：普遍再構成の図式頂点での値は個別に選んだ分類図式と同型。
方針：普遍表現をその図式へ cartesian に制限し表現空間内で比較する。
規約：普遍自己写像の実際の作用を比較し点ごとの新たな自己写像を作らない。
使われ方：全図式の比較を選択した分類の成分へ戻す。 -/
def universalCoherentReconstructionComponentIso {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) :
    VertexIso ((universalCoherentReconstructionMap B).app _ (functorVertex F))
      (functorVertex (smallFiberLeftStraighteningDiagram (leftUnstraighteningProjection F)
        (leftUnstraighteningProjection_hasSmallSimplexFibers F))) := by
  let U := uncurry (𝟙 ((ihom B).obj SpaceInfinity.{u}))
  let g : B ⟶ B ⊗ (ihom B).obj SpaceInfinity.{u} :=
    lift (𝟙 B) (SSet.const (functorVertex F))
  have h : g ≫ U = F := by
    rw [uncurry_at_vertex]
    exact (functorVertexEquiv B SpaceInfinity).symm_apply_apply F
  have e := coherentStraighteningRestrictionDiagramIso F U g h
  have hv : functorVertex
      (g ≫ smallFiberLeftStraighteningDiagram (leftUnstraighteningProjection U)
        (leftUnstraighteningProjection_hasSmallSimplexFibers U)) =
      (universalCoherentReconstructionMap B).app _ (functorVertex F) := by
    have hv := functorVertex_uncurry_at_vertex (universalCoherentReconstructionMap B)
      (functorVertex F)
    simpa only [universalCoherentReconstructionMap, uncurry_curry, g, U] using hv
  exact (eqToIso (congrArg SSet.HomotopyCategory.mk hv)).symm ≪≫ e.symm

end SerrePositivity.InfinityCategories
