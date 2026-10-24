module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationCornerRebuild
public import SerrePositivity.InfinityCategories.F2.Ind.IndCommaRelativeCocone
public import SerrePositivity.InfinityCategories.F2.Ind.RelativeCommaTransport
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationOldFamilyIso
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationExistence
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeExistenceTransport
public import SerrePositivity.InfinityCategories.Core.InnerPullback
/-!
概要：元の射図式族と指定終点変換を同時に延長する実 under comma の余錐。
方針：指定変換を旧族へ輸送して補間領域に貼り、同じ旧族の比較で元の全族へ戻す。
規約：元の q と指定変換を保持し、追加の Kan 性やモデル圏仮定を要求しない。
使われ方：終点評価の coslice 引き戻しの filtered 性と cofinal 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C)
local notation "E" => diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
/-- 概要：元の全族と指定終点変換を延長する、同じ実 under comma の余錐が存在する。
方針：共同余錐で拡張を選び直し、同じ旧族との同型を使う。
規約：元の全族と指定値を保持。使われ方：終点評価の cofinal 性。 -/
lemma nonempty_indArrowTargetUnder_cocone {A L : SSet.{u}}
    (hA : IsKappaSmall κ A) (hL : IsKappaSmall κ L)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶
      leftKanShape (indYoneda κ C)
        (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))))
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D)
    (t : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder z)
    (ht : q ≫ E = t ≫ sliceUnderProjection z) :
    Nonempty (JoinCocone (relativeCommaFamily E z t q ht)) := by
  obtain ⟨V₀⟩ := indArrowInterpolationData_nonempty κ D hA q
  obtain ⟨d₀⟩ := nonempty_indArrowInterpolationOldFamily_iso V₀
  obtain ⟨t', hf, hd⟩ := exists_relativeCommaFamily_iso_of_functorIso E z
    (indArrowInterpolationOldFamily V₀) q t ht d₀
  obtain ⟨c, cT, hCT⟩ := exists_indComma_relative_cocones κ
    (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (arrowInterpolationTargetInclusion A) hA
    (arrowInterpolationCorner_isKappaSmall (Fact.out : κ.IsRegular) hA) hL
    (indArrowInterpolationCornerFamily V₀) z t'
    ((indArrowInterpolationCornerFamily_target V₀).trans hf)
  let V := V₀.withCornerCocone c
  let P := (uliftCoconeShapeIso.{u, u + 1} A 0).hom ≫ cT.val
  have hP : (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫ P = t' := by
    dsimp only [P]
    rw [← Category.assoc, uliftCoconeShapeIso_inl, cT.property]
  have hV : indArrowInterpolationCommaFamily V ≫ E = P ≫ sliceUnderProjection z := by
    simp only [V, P, indArrowInterpolationCornerCocone_target, Category.assoc, hCT]
  let U := relativeCommaFamily E z P (indArrowInterpolationCommaFamily V) hV
  have hU : (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫ U =
      relativeCommaFamily E z t' (indArrowInterpolationOldFamily V₀) hf := by
    apply pullback.hom_ext
    · simp only [U, relativeCommaFamily, Category.assoc, pullback.lift_fst]
      exact hP
    · simp only [U, relativeCommaFamily, Category.assoc, pullback.lift_snd]
      exact indArrowInterpolationOldFamily_withCornerCocone V₀ c
  have hc : Nonempty (JoinCocone
      (relativeCommaFamily E z t' (indArrowInterpolationOldFamily V₀) hf)) :=
    ⟨⟨(uliftCoconeShapeIso.{u, u + 1} A 0).inv ≫ U, by
      rw [← Category.assoc, uliftCoconeShapeIso_inv_inl]
      exact hU⟩⟩
  exact nonempty_joinCocone_of_functorIso hd.some hc
end SerrePositivity.InfinityCategories.F2.Ind
