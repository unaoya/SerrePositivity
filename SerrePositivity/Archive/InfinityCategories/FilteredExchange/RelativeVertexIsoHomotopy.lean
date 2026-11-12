module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative

/-!
概要：相対写像空間の指定同型を、底を全時刻で固定する実際の円柱に表示する。
方針：相対空間内で辺を選び、包含後で uncurry する。
規約：元の相対同型の類と底の等式を保持。使われ方：全空間の fiberwise 引き戻し比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の相対同型を表す、底を固定した円柱と指定類の一致のデータ。
方針：相対空間の辺を包含して円柱へ戻す。
規約：全単体・全時刻で底を固定。使われ方：元の底上の path の実現。 -/
def relativeVertexIsoHomotopy {A E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    (a : A ⟶ B) {f g : A ⟶ E} (hf : f ≫ p = a) (hg : g ≫ p = a)
    (e : VertexIso (relativeFunctorVertex p a f hf) (relativeFunctorVertex p a g hg)) :
    {H : SSet.Homotopy f g //
      H.h ≫ p = fst A (Δ[1] : SSet.{u}) ≫ a ∧
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) =
          (e.map (vertexFiberι ((ihom A).map p) (functorVertex a))).hom} := by
  let k := Classical.choose (homotopyCategory_homMk_surjective _ _ e.hom)
  have hk := Classical.choose_spec (homotopyCategory_homMk_surjective _ _ e.hom)
  let i := vertexFiberι ((ihom A).map p) (functorVertex a)
  let j := k.map ((truncation 2).map i)
  let H : SSet.Homotopy f g := simplicialHomotopyOfFunctorEdge j
  have hH : H.h = relativeFunctorUncurry (SSet.yonedaEquiv.symm k.edge) := by
    change uncurry (SSet.yonedaEquiv.symm (i.app (Opposite.op ⦋1⦌) k.edge)) =
      uncurry (SSet.yonedaEquiv.symm k.edge ≫ i)
    rw [SSet.yonedaEquiv_symm_comp]
    rfl
  refine ⟨H, ?_, ?_⟩
  · rw [hH]
    exact relativeFunctorUncurry_projection _
  · have he : functorEdgeOfSimplicialHomotopy H = j := by
      apply SSet.Truncated.Edge.ext
      change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm j.edge))) = j.edge
      rw [curry_uncurry, Equiv.apply_symm_apply]
    rw [he]
    change (SSet.Truncated.mapHomotopyCategory ((truncation 2).map i)).map
      (SSet.Truncated.HomotopyCategory.homMk k) = _
    rw [hk]
    rfl

end SerrePositivity.InfinityCategories.F2
