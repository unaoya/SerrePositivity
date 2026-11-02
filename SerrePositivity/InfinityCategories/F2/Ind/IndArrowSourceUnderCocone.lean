module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationUnderFamily
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationUnderSource
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.CoconeExistenceTransport
/-!
概要：指定始点評価図式の下で、元の実試験族を延長する相対余錐を構成する。
方針：同じ下側変換を持つ補間全族の余錐を、実 under comma 内の同型で戻す。
規約：元の q と指定下側変換を全パラメーターで保持する。
使われ方：始点評価の coslice 引き戻しの filtered 性。
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
local notation "E" => diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
/-- 概要：元の全族と指定下側変換を延長する実 under comma の余錐が存在する。
方針：補間余錐を同じ相対同型で戻す。規約：元の全族を保持。使われ方：cofinal 性。 -/
lemma nonempty_indArrowSourceUnder_cocone {A L : SSet.{u}}
    (hA : IsKappaSmall κ A) (hL : IsKappaSmall κ L)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶
      leftKanShape (indYoneda κ C)
        (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))))
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D)
    (t : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder z)
    (ht : q ≫ E = t ≫ sliceUnderProjection z) :
    Nonempty (JoinCocone (relativeCommaFamily E z t q ht)) := by
  obtain ⟨V, P, hP, hVP⟩ := exists_indArrowInterpolationData_under_source κ D hA hL z q t ht
  obtain ⟨d⟩ := nonempty_indArrowInterpolationOldFamily_under_iso V z t ht
  exact nonempty_joinCocone_of_functorIso d
    ⟨indArrowInterpolationUnderOldFamilyCocone V z t ht P hP hVP⟩
/-- 概要：実 coslice 引き戻しの任意の小さい試験族は、その元の族への余錐を持つ。
方針：二射影の族を構成して戻す。規約：元の族を厳密に回収。使われ方：filtered 性。 -/
lemma nonempty_indArrowSourceEvaluationComma_cocone {A L : SSet.{u}}
    (hA : IsKappaSmall κ A) (hL : IsKappaSmall κ L)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶
      leftKanShape (indYoneda κ C)
        (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))))
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ pullback (sliceUnderProjection z) E) :
    Nonempty (JoinCocone q) := by
  have h : (q ≫ pullback.snd (sliceUnderProjection z) E) ≫ E =
      (q ≫ pullback.fst (sliceUnderProjection z) E) ≫ sliceUnderProjection z := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hc := nonempty_indArrowSourceUnder_cocone κ D hA hL z
    (q ≫ pullback.snd (sliceUnderProjection z) E)
    (q ≫ pullback.fst (sliceUnderProjection z) E) h
  have hq : relativeCommaFamily E z (q ≫ pullback.fst (sliceUnderProjection z) E)
      (q ≫ pullback.snd (sliceUnderProjection z) E) h = q := by
    apply pullback.hom_ext <;> simp only [relativeCommaFamily, pullback.lift_fst,
      pullback.lift_snd]
  exact hq ▸ hc
end SerrePositivity.InfinityCategories.F2.Ind
