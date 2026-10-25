module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.CartesianInitialBoundary
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeInitialBoundaryCriterion
public import SerrePositivity.InfinityCategories.Core.PinchedUniversal
public import SerrePositivity.InfinityCategories.Core.ContractibleKan
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialFiberEdgePiZero

/-!
概要：始対象を始域とする対象上の射は、その slice の始対象である。
方針：始対象からの写像空間の可縮性を fiber に移し、相対境界充填を使う。
規約：元の射を変更せず、全境界の充填として結論する。
使われ方：対象上の余錐の余極限性を底の余極限性から回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：相対始点境界充填を持つ頂点の像が始対象なら、元も始対象。
方針：底で境界を充填し、その指定単体の上で境界を持ち上げる。
規約：ファイブレーションの追加仮定は不要。
使われ方：fiber の始対象から全空間の始対象への移送。 -/
lemma isInitialVertex_of_initialBoundaryLifting_of_image {E B : SSet.{u}}
    (p : E ⟶ B) (x : E _⦋0⦌) (hx : InitialBoundaryLifting p x)
    (hb : IsInitialVertex (p.app (Opposite.op ⦋0⦌) x)) : IsInitialVertex x := by
  intro n a ha
  have hab : boundaryVertex n 0 ≫ (a ≫ p) =
      SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x) := by
    rw [← Category.assoc, ha, SSet.yonedaEquiv_symm_comp]
  obtain ⟨b, hbound⟩ := hb n (a ≫ p) hab
  obtain ⟨F, hF, _⟩ := hx n a b ha ⟨hbound.symm⟩
  exact ⟨F, hF⟩

/-- 概要：対象上の射の始域が始対象なら、その射も slice の始対象。
方針：始対象からの Hom の可縮性で fiber の始対象を得て、相対境界を充填する。
規約：slice の元の頂点を保持する。
使われ方：対象上の colimit の底への射影による検出。 -/
lemma isInitialVertex_sliceOver_of_source {X : SSet.{u}} [Quasicategory X]
    (y : X _⦋0⦌) (v : (sliceOver (SSet.yonedaEquiv.symm y)) _⦋0⦌)
    (hv : IsInitialVertex
      ((sliceOverProjection (SSet.yonedaEquiv.symm y)).app (Opposite.op ⦋0⦌) v)) :
    IsInitialVertex v := by
  let p := sliceOverProjection (SSet.yonedaEquiv.symm y)
  let x := p.app (Opposite.op ⦋0⦌) v
  let w := initialFiberVertexAt p v x rfl
  have hc : IsContractibleKan (vertexFiber p x) :=
    isContractibleKan_of_iso (pinchedHomSliceFiberIso x y)
      (F1B.kanInitialVertex_pinchedHom_isContractibleKan hv y)
  have hw := F1B.initialBoundaryLifting_of_isInitialVertex_fiber p x w
    (hc.isInitialVertex w)
  exact isInitialVertex_of_initialBoundaryLifting_of_image p v hw hv

end SerrePositivity.InfinityCategories.F2.Presentable
