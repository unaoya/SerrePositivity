module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationOldCocone
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationDiagramBoundary
/-!
概要：同じ slice 円柱を保って補間の終点拡張を選び直しても、元の旧族は変わらない。
方針：元の小さい図式への射影と全余錐の二成分を厳密に回収する。
規約：始点余錐・元の円柱・旧族を全て保持する。
使われ方：終点評価の指定変換を取り込んだ補間余錐の再構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
/-- 概要：同じ元の slice 円柱から得た旧族は、終点拡張の選択に依存しない。
方針：実 comma の二成分で確認する。規約：厳密な等式。使われ方：指定変換の追加。 -/
lemma indArrowInterpolationOldFamily_eq_of_slicePrism (V V' : IndArrowInterpolationData κ D q)
    (h : V.slicePrism.val = V'.slicePrism.val) :
    indArrowInterpolationOldFamily V = indArrowInterpolationOldFamily V' := by
  apply pullback.hom_ext
  · change indArrowInterpolationOldFamily V ≫ diagramCommaProjection κ D =
      indArrowInterpolationOldFamily V' ≫ diagramCommaProjection κ D
    simp only [indArrowInterpolationOldFamily, Category.assoc,
      indArrowInterpolationCommaFamily_old_projection]
  · apply sliceOverUncurry_injective
    change sliceOverUncurry (indArrowInterpolationOldFamily V ≫ diagramCommaSliceProjection κ D) =
      sliceOverUncurry (indArrowInterpolationOldFamily V' ≫ diagramCommaSliceProjection κ D)
    rw [indArrowInterpolationOldFamily_uncurry, indArrowInterpolationOldFamily_uncurry, h]
variable (V : IndArrowInterpolationData κ D q)
  (E : (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}) ⊗ Δ[1]) ⟶
    leftKanShape (indYoneda κ C)
      (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))))
  (hOld : (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ E =
    (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ V.extension)
  (hSource : (SSet.uliftFunctor.{u + 1, u}).map SSet.ι₀ ≫ E =
    (SSet.uliftFunctor.{u + 1, u}).map SSet.ι₀ ≫ V.extension)
/-- 概要：元の全旧境界と始点境界を保って、同じデータの終点拡張だけを選び直す。
方針：同じ始点余錐と slice 円柱を使う。規約：元の指定値を保持。使われ方：相対補間。 -/
def IndArrowInterpolationData.withExtension : IndArrowInterpolationData κ D q :=
  { V with extension := E, old := hOld.trans V.old, source := hSource.trans V.source }

/-- 概要：終点拡張を選び直したデータの元の旧族は、元の旧族そのもの。
方針：同じ slice 円柱の不変性を使う。規約：厳密な等式。使われ方：比較の再利用。 -/
lemma indArrowInterpolationOldFamily_withExtension :
    indArrowInterpolationOldFamily (V.withExtension E hOld hSource) =
      indArrowInterpolationOldFamily V :=
  indArrowInterpolationOldFamily_eq_of_slicePrism _ _ rfl
end SerrePositivity.InfinityCategories.F2.Ind
