module

public import SerrePositivity.InfinityCategories.F1.FilteredExchange.ColimitHomotopyPointwise
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationCocone

/-!
概要：元の余極限余錐の像の比較は、基底の各値で可逆なら指定頂点でも可逆。
方針：同じ自然ホモトピーを全余錐へ前合成し、既存の余極限の点ごとの可逆性を適用する。
規約：元の指定比較辺と元の頂点を保持する。
使われ方：κ-filtered 生成表示による制限射の同値の検出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

lemma homotopy_colimit_value_isInvertible {K X Y : SSet.{u}} [Quasicategory Y]
    {p : K ⟶ X} (c : JoinCocone p) {F G : X ⟶ Y}
    (hF : IsColimitCone (mapJoinCocone F c)) (hG : IsColimitCone (mapJoinCocone G c))
    (H : SSet.Homotopy F G)
    (hH : ∀ j, IsInvertibleEdge
      (simplicialHomotopyVertexEdge H (p.app (Opposite.op ⦋0⦌) j)).toTruncated) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge H c.vertex).toTruncated := by
  let H' := stableHomotopyPrecomp c.val H
  have hp : ∀ j, IsInvertibleEdge (simplicialHomotopyVertexEdge H'
      ((joinInl K Δ[0]).app (Opposite.op ⦋0⦌) j)).toTruncated := by
    intro j
    apply (isInvertibleEdge_congr (F2.homotopyVertexEdge_precomp c.val H _)).mpr
    have hx : c.val.app (Opposite.op ⦋0⦌)
        ((joinInl K Δ[0]).app (Opposite.op ⦋0⦌) j) = p.app (Opposite.op ⦋0⦌) j :=
      ConcreteCategory.congr_hom (NatTrans.congr_app c.property (Opposite.op ⦋0⦌)) j
    exact Eq.mpr (congrArg (fun w =>
      IsInvertibleEdge (simplicialHomotopyVertexEdge H w).toTruncated) hx) (hH j)
  have ht := F2.colimitHomotopy_vertex_isInvertible (mapJoinCocone F c) (mapJoinCocone G c)
    hF hG H' hp
  have ht' := (isInvertibleEdge_congr (F2.homotopyVertexEdge_precomp c.val H _)).mp ht
  have hx : c.val.app (Opposite.op ⦋0⦌)
      ((joinInr K Δ[0]).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 Δ[0]))) = c.vertex := rfl
  exact Eq.mp (congrArg (fun w =>
    IsInvertibleEdge (simplicialHomotopyVertexEdge H w).toTruncated) hx) ht'

end SerrePositivity.InfinityCategories.F2.Ind
