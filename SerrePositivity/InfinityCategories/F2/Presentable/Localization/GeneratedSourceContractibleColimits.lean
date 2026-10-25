module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.SourceCosliceProjectionColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.SourceArrowFiber
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedArrowColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.SourceCosliceColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedConstantColimitPreservation
public import SerrePositivity.InfinityCategories.F2.Ind.PreservedColimitRestriction

/-!
概要：固定始域の閉包内射は、弱可縮な通常圏の指定小余極限で閉じる。
方針：全脚族の始点を定値余極限、終域を coslice の余極限として射圏へ移す。
規約：全脚族の同じ余錐の普遍性を使い、内部の余極限もその同じ余錐から構成する。
使われ方：HTT 5.5.5.11 の filtered・pushout 形状における閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- cofinal な定値始域と終域計算により、元の coslice の余極限は閉包内に残る。 -/
lemma generatedSource_colimit_mem_of_cofinal (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    {K : SSet.{u}} [Quasicategory K]
    (hpoint : IsRightCofinal (stdSimplex.isTerminalObj₀.from
      ((SSet.uliftFunctor.{u + 1, u}).obj K)))
    (hr : IsRightCofinal (joinInr (Δ[0] : SSet.{u + 1})
      ((SSet.uliftFunctor.{u + 1, u}).obj K)))
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ generatedSourceCategory edges x)
    (c : JoinCocone (D ≫ generatedSourceInclusion edges x)) (hc : IsColimitCone c) :
    (JoinCocone.leg c.vertex (𝟙 Δ[0])).edge ∈ generatedEdges edges := by
  let B := D ≫ generatedSourceArrows edges x
  let cA : JoinCocone (B ≫ generatedArrowInclusion edges) :=
    ⟨c.val ≫ sourceCosliceArrowFamily x, by
      rw [← Category.assoc, c.property, Category.assoc,
        ← generatedSourceArrows_inclusion]
      rfl⟩
  have h₀ : IsColimitCone (mapJoinCocone
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)) cA) := by
    have h := constantJoinCocone_isColimit_of_pointCofinal hpoint x
    apply (isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr h
    change (c.val ≫ sourceCosliceArrowFamily x) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = SSet.const x
    rw [Category.assoc, sourceCosliceArrowFamily_source, SSet.comp_const]
  have h₁ : IsColimitCone (mapJoinCocone
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1)) cA) := by
    have h := (sourceCoslice_isColimitCone_iff_projection (SSet.yonedaEquiv.symm x)
      (D ≫ generatedSourceInclusion edges x) hr c).mp hc
    apply (isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr h
    change (c.val ≫ sourceCosliceArrowFamily x) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) = c.val ≫ sliceUnderProjection _
    rw [Category.assoc, sourceCosliceArrowFamily_target]
  have hA : IsColimitCone cA := by
    apply isColimitCone_of_pointwise
    intro a
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective a
    fin_cases i
    · exact h₀
    · exact h₁
  have hm := generatedArrow_colimit_mem edges B cA hA
  change arrowVertexEdge ((sourceCosliceArrowFamily x).app _ c.vertex) ∈ generatedEdges edges
    at hm
  rwa [sourceCosliceArrowFamily_vertex] at hm

/-- 弱可縮な小さい通常圏の全指定余極限は、固定始域の閉包内に留まる。 -/
lemma generatedSource_nerve_colimit_mem (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (J : Type u) [SmallCategory J] (hJ : IsWeaklyContractible (nerve J))
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ generatedSourceCategory edges x)
    (c : JoinCocone (D ≫ generatedSourceInclusion edges x)) (hc : IsColimitCone c) :
    (JoinCocone.leg c.vertex (𝟙 Δ[0])).edge ∈ generatedEdges edges :=
  generatedSource_colimit_mem_of_cofinal edges x (pointProjection_ulift_isRightCofinal hJ)
    (sourceJoinInr_ulift_nerve_isRightCofinal J hJ) D c hc

/-- 同じ周囲の余錐を持ち上げ、弱可縮な通常圏形状の余極限を内部にも構成する。 -/
lemma generatedSource_hasNerveColimit (hC : HasSmallColimits C)
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (J : Type u) [SmallCategory J] (hJ : IsWeaklyContractible (nerve J))
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ generatedSourceCategory edges x) :
    Ind.HasPreservedColimit (generatedSourceInclusion edges x) D := by
  obtain ⟨c, hc⟩ := sourceCoslice_hasSmallColimits hC x (nerve J)
    (D ≫ generatedSourceInclusion edges x)
  let P := fun c : (sliceUnder (SSet.yonedaEquiv.symm x)) _⦋0⦌ ↦
    (JoinCocone.leg c (𝟙 Δ[0])).edge ∈ generatedEdges edges
  have hm : P c.vertex := generatedSource_nerve_colimit_mem edges x J hJ D c hc
  refine ⟨Ind.fullCoconeLift P D c hm, Ind.fullCoconeLift_isColimit P D c hm hc, ?_⟩
  have hi : mapJoinCocone (generatedSourceInclusion edges x) (Ind.fullCoconeLift P D c hm) = c :=
    Ind.fullCoconeLift_inclusion P D c hm
  exact hi.symm ▸ hc

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
