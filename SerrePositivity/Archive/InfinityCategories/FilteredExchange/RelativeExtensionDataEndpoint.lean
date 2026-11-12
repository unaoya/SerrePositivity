module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionDataIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.VertexIsoTerminalEquality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorExtensionEndpoint

/-!
概要：底と初期値の明示移送は、同じ引き戻しを標的とする実際の終点評価と交換する。
方針：元の全単体を保つ移送の定義を使い、指定同型の像へ厳密な交換式を適用する。
規約：全パラメータと指定値を保持。使われ方：共通 prism 空間から元の fiber 比較への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A D C E F B : SSet.{u}} (p : E ⟶ B) (b b' : A ⟶ B) (i : D ⟶ A)
  (v v' : D ⟶ E) (hv : v ≫ p = i ≫ b) (hv' : v' ≫ p = i ≫ b')
  (hb : b = b') (he : v = v') (j : C ⟶ A) (q : F ⟶ B) (a : C ⟶ F)
  (hj : j ≫ b = a ≫ q) (hj' : j ≫ b' = a ≫ q)

/-- 元の全延長を保持する底・初期値の移送は、実際の引き戻し終点評価と厳密に交換。 -/
lemma relativeExtensionDataIso_endpoint :
    (relativeExtensionDataIso p b b' i v v' hv hv' hb he).hom ≫
      relativeFunctorExtensionEndpoint p b' i v' hv' j q a hj' =
    relativeFunctorExtensionEndpoint p b i v hv j q a hj := by
  subst b'
  subst v'
  rfl

/-- 移送後の同じ終点評価へ写した指定同型は、元の指定終点同型と値まで一致する。 -/
lemma relativeExtensionDataIso_endpoint_vertexIso
    {x y : (relativeFunctorExtensionSpace p b i v hv) _⦋0⦌} (e : VertexIso x y) :
    HEq
      (VertexIso.map (VertexIso.map e
        (relativeExtensionDataIso p b b' i v v' hv hv' hb he).hom)
        (relativeFunctorExtensionEndpoint p b' i v' hv' j q a hj'))
      (VertexIso.map e (relativeFunctorExtensionEndpoint p b i v hv j q a hj)) := by
  exact (heq_of_eq (vertexIso_map_comp e
    (relativeExtensionDataIso p b b' i v v' hv hv' hb he).hom
    (relativeFunctorExtensionEndpoint p b' i v' hv' j q a hj'))).trans
      (vertexIso_map_heq e
        (relativeExtensionDataIso_endpoint p b b' i v v' hv hv' hb he j q a hj hj'))

end SerrePositivity.InfinityCategories.F2
