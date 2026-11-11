module
public import SerrePositivity.KST.SConstruction.CoherentTetrahedronWhiskeredEdges

/-! # 元の豊穣比較辺と固定射の全合成辺
概要：元の長辺から二射の合成への比較辺を、固定した第一射・最終射と実合成する。
方針：元の辺と固定頂点の恒等辺の積を豊穣合成で写し、頂点の合成式で両端を合わせる。
規約：元の全比較辺を保持する。三射の括弧の表示は圏の合成則で厳密に合わせる。
使われ方：同じ BF 写像空間内の二経路を元の辺を持つ実合成三角形へ束ねる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の後半比較辺を固定した第一射と合成し、同じ三射合成の頂点へ向ける。 -/
def enrichedComparisonLeftWhisker {W X Y Z : C} (f : W ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) (gh : X ⟶ Z)
    (e : (SimplicialCategory.sHom X Z).Edge (SimplicialCategory.homEquiv' _ _ gh)
      (SimplicialCategory.homEquiv' _ _ (g ≫ h))) :
    (SimplicialCategory.sHom W Z).Edge (SimplicialCategory.homEquiv' _ _ (f ≫ gh))
      (SimplicialCategory.homEquiv' _ _ ((f ≫ g) ≫ h)) :=
  ((SSet.Edge.ofTruncated ((SSet.Edge.id (SimplicialCategory.homEquiv' W X f)).toTruncated.tensor
    e.toTruncated)).map (SimplicialCategory.sHomComp W X Z)).ofEq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_vertex_comp f gh).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_vertex_comp f (g ≫ h)).symm.trans
      (congrArg (SimplicialCategory.homEquiv' W Z) (Category.assoc f g h).symm))

/-- 左合成は元の比較辺全体と固定した恒等辺を同じ豊穣合成で写した全一単体。 -/
lemma enrichedComparisonLeftWhisker_edge {W X Y Z : C} (f : W ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) (gh : X ⟶ Z)
    (e : (SimplicialCategory.sHom X Z).Edge (SimplicialCategory.homEquiv' _ _ gh)
      (SimplicialCategory.homEquiv' _ _ (g ≫ h))) :
    (enrichedComparisonLeftWhisker f g h gh e).edge =
      (SimplicialCategory.sHomComp W X Z).app (Opposite.op ⦋1⦌)
        ((SSet.Edge.id (SimplicialCategory.homEquiv' W X f)).edge, e.edge) := rfl

/-- 元の前半比較辺を固定した最終射と合成し、同じ三射合成の頂点へ向ける。 -/
def enrichedComparisonRightWhisker {W X Y Z : C} (f : W ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) (fg : W ⟶ Y)
    (e : (SimplicialCategory.sHom W Y).Edge (SimplicialCategory.homEquiv' _ _ fg)
      (SimplicialCategory.homEquiv' _ _ (f ≫ g))) :
    (SimplicialCategory.sHom W Z).Edge (SimplicialCategory.homEquiv' _ _ (fg ≫ h))
      (SimplicialCategory.homEquiv' _ _ ((f ≫ g) ≫ h)) :=
  ((SSet.Edge.ofTruncated (e.toTruncated.tensor
    (SSet.Edge.id (SimplicialCategory.homEquiv' Y Z h)).toTruncated)).map
      (SimplicialCategory.sHomComp W Y Z)).ofEq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_vertex_comp fg h).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_vertex_comp (f ≫ g) h).symm

/-- 右合成も元の比較辺全体と固定した恒等辺を同じ豊穣合成で写した全一単体。 -/
lemma enrichedComparisonRightWhisker_edge {W X Y Z : C} (f : W ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) (fg : W ⟶ Y)
    (e : (SimplicialCategory.sHom W Y).Edge (SimplicialCategory.homEquiv' _ _ fg)
      (SimplicialCategory.homEquiv' _ _ (f ≫ g))) :
    (enrichedComparisonRightWhisker f g h fg e).edge =
      (SimplicialCategory.sHomComp W Y Z).app (Opposite.op ⦋1⦌)
        (e.edge, (SSet.Edge.id (SimplicialCategory.homEquiv' Y Z h)).edge) := rfl

end SerrePositivity.KST.SConstruction
