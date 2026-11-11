module

public import SerrePositivity.EInfinity.BarrattEccles.CAlgAlgebraSource

/-!
# 元の E 代数の擬同型の CAlg_R での反転

概要：cofibrancy を仮定しない元の代数射の擬同型から同じ代数頂点の同型を得る。
方針：元の関手的置換を同じ局所化源へ送り、元の辺の反転を使う。
規約：既存 algebraCAlgSource と cAlgVertex の頂点比較を保持する。
使われ方：零次模型の擬同型 span と離散像の頂点同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet HomotopicalAlgebra
open SerrePositivity.InfinityCategories SimplicialLocalization
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma algebraCAlgSource_map_weak {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk f).map (algebraCAlgSource A)).toTruncated := by
  let g := (cofibrantAlgebraDKReplacement A).map f
  have hg : (cofibrantAlgebraRelativeCategory A).weakEquivalences g := by
    let := modelCategory A
    exact (cofibrantAlgebraDKReplacementRelative A).map _ hf
  have h := cAlgLocalizationSource_inverts A
    (show ComposableArrows.mk₁ g ∈ weakNerveEdges (cofibrantAlgebraRelativeCategory A) from
      ⟨_, _, g, hg, rfl⟩)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := CAlg_R A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ComposableArrows.mk₁ g)).map
    ((truncation 2).map (cAlgLocalizationSource A))) at h
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ComposableArrows.mk₁ g)).map
      ((truncation 2).map (cAlgLocalizationSource A)))
    (f := ((nerve.edgeMk f).map (algebraCAlgSource A)).toTruncated) ?_).mp h
  change (cAlgLocalizationSource A).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ g) =
    (algebraCAlgSource A).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f)
  apply congrArg ((cAlgLocalizationSource A).app (Opposite.op ⦋1⦌))
  exact ComposableArrows.ext₁ (C := (cofibrantAlgebraRelativeCategory A).category)
    rfl rfl (by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)

def cAlgVertexIsoOfQuasiIso {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (cAlgVertex A X) (cAlgVertex A Y) := by
  have := algebraCAlgSource_map_weak A f hf
  exact (algebraCAlgSource_vertexIso A X).symm ≪≫
    asIso (Truncated.HomotopyCategory.homMk
      ((nerve.edgeMk f).map (algebraCAlgSource A)).toTruncated) ≪≫
        algebraCAlgSource_vertexIso A Y

end SerrePositivity.EInfinity.BarrattEccles
