module
public import SerrePositivity.KST.SConstruction.PointedMappingCompositionFamilies
public import SerrePositivity.KST.SConstruction.KanAssemblyMixedFamily
public import SerrePositivity.KST.SConstruction.InverseMixedFamilyTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdgeInterchange

/-! # 二本の入力にまたがる逆射・延長の中間交換
概要：最初の入力の逆射の混合族と次の入力の延長の混合族を合成する。
方針：中間の Kan 模型を共有する写像空間の豊穣合成と直積三角形を使う。
規約：二つの指定した辺を動かす順序を比較する。
使われ方：構造射の自然性ホモトピーの合成の二次比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra Spectra.PointedMapping
open scoped Simplicial

/-- 最初の逆射の混合選択と次の延長の混合選択を同時に合成する族。 -/
def assemblyCrossedFamily (r : ℕ) {X Y Z : StableModel.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    oneDirectionInverseMixedChoices r f ⊗ kanAssemblyMixedChoices r g ⟶
      (PointedObject.basedHom ((boundaryKanRealizationFunctor r).obj X)
        ((loopBoundaryKanFunctor (r + 1)).obj Z)).right :=
  (oneDirectionInverseMixedFamily r f ⊗ₘ kanAssemblyMixedFamily r g) ≫
    pointedMappingComposition _ _ _

/-- 指定した逆射側・延長側の辺の中間交換は実際の二つの三角形で一致する。 -/
lemma assemblyCrossedFamily_edge_interchange (r : ℕ)
    {X Y Z : StableModel.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {i₀ i₁ : (oneDirectionInverseMixedChoices r f) _⦋0⦌}
    {e₀ e₁ : (kanAssemblyMixedChoices r g) _⦋0⦌}
    (a : (oneDirectionInverseMixedChoices r f).Edge i₀ i₁)
    (b : (kanAssemblyMixedChoices r g).Edge e₀ e₁) :
    SSet.HomotopyCategory.homMk ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair a (.id e₀)).map (assemblyCrossedFamily r f g)) ≫
      SSet.HomotopyCategory.homMk ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (.id i₁) b).map (assemblyCrossedFamily r f g)) =
    SSet.HomotopyCategory.homMk ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (.id i₀) b).map (assemblyCrossedFamily r f g)) ≫
      SSet.HomotopyCategory.homMk ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair a (.id e₁)).map (assemblyCrossedFamily r f g)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgeInterchange (assemblyCrossedFamily r f g) a b

/-- 逆射側の指定した混合選択と延長側の指定した混合選択の合成の頂点。 -/
lemma assemblyCrossedFamily_vertex (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : (oneDirectionInverseMixedChoices r f) _⦋0⦌)
    (b : (kanAssemblyMixedChoices r g) _⦋0⦌) :
    (assemblyCrossedFamily r f g).app (Opposite.op ⦋0⦌) (a, b) =
      familyVertex (oneDirectionInverseMixedMap r f a ≫ kanAssemblyMixedMap r g b) := by
  change (pointedMappingComposition _ _ _).app (Opposite.op ⦋0⦌)
    ((oneDirectionInverseMixedFamily r f).app _ a, (kanAssemblyMixedFamily r g).app _ b) = _
  have hb : (kanAssemblyMixedFamily r g).app (Opposite.op ⦋0⦌) b =
      familyVertex (kanAssemblyMixedMap r g b) := (familyVertex_familyMap _ _ _).symm
  rw [oneDirectionInverseMixedFamily_vertex, hb, pointedMappingComposition_vertex]

end SerrePositivity.KST.SConstruction
