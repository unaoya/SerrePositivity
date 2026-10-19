module
public import SerrePositivity.InfinityCategories.Derived.CofiberSuspensionSquareHom
public import SerrePositivity.InfinityCategories.Derived.ComplexSquareMiddleComponents
public import SerrePositivity.InfinityCategories.Derived.ComplexSquareHomEvaluation
public import SerrePositivity.InfinityCategories.Stable.ArrowIdentityComposition

/-! # Cofiber から suspension の四角形比較の両端成分

概要：二段比較の始点は恒等射、終点は標準 cone 写像になる。
方針：中間対象の変更の恒等成分を消し、後合成比較の成分を使う。
規約：端点表示の等式も Arrow に含める。使われ方：D7 の接続射の一意性への適用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial ZeroObject
variable {S : Type u} [CommRing S] {A B : Complex S}

/-- 正規化した中間対象比較の両端成分は恒等射。 -/
lemma cofiberToSuspensionMiddleHomotopy_corner_arrow (f : A ⟶ B) (i : Fin 2) :
    Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) i i).map
      (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (cofiberToSuspensionMiddleHomotopy f)))) =
      Arrow.mk (𝟙 (squareHoVertex
        ((cofiberComplexSquareData f (0 : A ⟶ 0)).postcompose (cofiberToSuspensionMap f)).square
          i i)) := by
  have h := ((cofiberComplexSquareData f (0 : A ⟶ 0)).postcompose
    (cofiberToSuspensionMap f)).changeBottomMiddleHomotopy_corner_arrow (0 : B ⟶ 0)
      (pushoutInclusionB (0 : A ⟶ 0) (0 : A ⟶ 0)) (cofiberToSuspensionRightFactor f) i
  refine Eq.trans ?_ h
  exact congrArg (squareDiagramHoEvaluation (dgNerve S (Complex S)) i i).mapArrow.obj
    (homotopyOfEndpoints_functorHom_arrow
      (((cofiberComplexSquareData f (0 : A ⟶ 0)).postcompose
        (cofiberToSuspensionMap f)).changeBottomMiddleHomotopy (0 : B ⟶ 0)
          (pushoutInclusionB (0 : A ⟶ 0) (0 : A ⟶ 0)) (cofiberToSuspensionRightFactor f)) rfl
      (congrArg (fun k : ComplexSquareData A 0 0
        (pushoutCofiber (0 : A ⟶ 0) (0 : A ⟶ 0)) => k.square)
          (cofiberToSuspensionIntermediateData_eq f)))

/-- 標準 cofiber から suspension の比較の始点成分は恒等射。 -/
lemma cofiberToSuspensionSquareHom_source_arrow (f : A ⟶ B) :
    Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 0 0).map
      (cofiberToSuspensionSquareHom f)) =
      Arrow.mk (𝟙 (squareHoVertex (cofiberComplexSquareData f (0 : A ⟶ 0)).square 0 0)) := by
  unfold cofiberToSuspensionSquareHom
  rw [CategoryTheory.Functor.map_comp]
  exact (arrowMk_comp_of_right_identity _ _
    (cofiberToSuspensionMiddleHomotopy_corner_arrow f 0)).trans
      (arrowMk_eq_id_source _
        ((cofiberComplexSquareData f (0 : A ⟶ 0)).postcomposeHom_source_arrow
          (cofiberToSuspensionMap f)))

/-- 標準 cofiber から suspension の比較の終点成分は指定した cone 写像。 -/
lemma cofiberToSuspensionSquareHom_target_arrow (f : A ⟶ B) :
    Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 1 1).map
      (cofiberToSuspensionSquareHom f)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (complexEdge (cofiberToSuspensionMap f)).toTruncated) := by
  unfold cofiberToSuspensionSquareHom
  rw [CategoryTheory.Functor.map_comp]
  exact (arrowMk_comp_of_right_identity _ _
    (cofiberToSuspensionMiddleHomotopy_corner_arrow f 1)).trans
      ((cofiberComplexSquareData f (0 : A ⟶ 0)).postcomposeHom_target_arrow
        (cofiberToSuspensionMap f))

end SerrePositivity.InfinityCategories
