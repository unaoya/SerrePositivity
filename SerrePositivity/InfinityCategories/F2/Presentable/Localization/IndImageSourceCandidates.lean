module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImage
public import SerrePositivity.InfinityCategories.F2.Presentable.PointFiberFilteredColimits
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullSubcomplexEquivalenceLifting
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorEvaluationLifting

/-!
概要：実 Ind 像の固定始域 fiber に、小さい compact 候補を構成する。
方針：実像の accessibility と端点評価の同値持ち上げ・filtered 保存を公開 fiber 版へ渡す。
規約：実像と全強飽和射圏の一致、候補の filtered 生成性は主張しない。
使われ方：f2 の強飽和性と独立に進める f3 の小さい候補の準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {κ : Cardinal.{u}} [Fact κ.IsRegular] {A : SSet.{u}} [Quasicategory A]
  {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}
  (edges : I → C _⦋1⦌) (G : Ind.IndInfinity κ A ⟶ generatedArrowCategory edges)

/-- 元の実 Ind 像の全部分包含は同値を持ち上げる。 -/
lemma indArrowImageInclusion_equivalenceLifting :
    F1B.EquivalenceLifting (indArrowImageInclusion edges G) :=
  kanEquivalenceLifting_fullSubcomplexOnVertices_ι _
    (fun e ↦ indArrowImageVertex_iff_vertexIso edges G e)

/-- 実像の各端点評価も同値を持ち上げる。 -/
lemma indArrowImageEvaluation_equivalenceLifting (a : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    F1B.EquivalenceLifting (indArrowImageInclusion edges G ≫ evaluateFunctorAt a) := by
  intro B D i hi he
  have := indArrowImageInclusion_equivalenceLifting edges G i hi he
  have := kanEquivalenceLifting_evaluateFunctorAt (X := C) a i hi he
  infer_instance

/-- 実比較の保存性から、元の実像の各端点評価の同じ濃度での保存性を得る。 -/
lemma indArrowImageEvaluation_isKappaAccessibleFunctor (hC : HasSmallColimits C)
    (hff : IsFullyFaithful G) (hG : IsKappaAccessibleFunctor κ G)
    (a : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    IsKappaAccessibleFunctor κ (indArrowImageInclusion edges G ≫ evaluateFunctorAt a) :=
  (indArrowImageInclusion_isKappaAccessible edges G hC hff hG).comp
    ((evaluateFunctorAt_preservesSmallColimits hC a).isKappaAccessibleFunctor κ)

/-- 任意の指定始域の実像 fiber に、元の成分 compact 点を被覆する小さい候補がある。 -/
lemma exists_indArrowImageSource_compactCandidate (hC : IsPresentable C)
    (hff : IsFullyFaithful G) (hG : IsKappaAccessibleFunctor κ G)
    (x : C _⦋0⦌) (σ : Cardinal.{u}) :
    let p := indArrowImageInclusion edges G ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)
    let q := SSet.yonedaEquiv.symm x
    letI := F1B.EquivalenceLifting.innerFibration
      (indArrowImageEvaluation_equivalenceLifting edges G (stdSimplex.obj₀Equiv.symm 0))
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧
      ∃ (B : SSet.{u}) (hB : Quasicategory B),
        letI := hB
        ∃ i : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ pullback p q,
          IsFullyFaithful i ∧
          (∀ b : B _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ (i.app _ (ULift.up b))) ∧
          (∀ b : B _⦋0⦌, ComponentCompactVertex μ p q (i.app _ (ULift.up b))) ∧
          ∀ z, ComponentCompactVertex μ p q z →
            ∃ b : B _⦋0⦌, Nonempty (VertexIso z (i.app _ (ULift.up b))) := by
  exact exists_accessibleFiber_compactCandidate
    (indArrowImage_isKappaAccessible edges G hff).isAccessible hC.1 _ _
    (indArrowImageEvaluation_equivalenceLifting edges G _)
    ⟨κ, Fact.out, indArrowImageEvaluation_isKappaAccessibleFunctor edges G hC.2 hff hG _⟩ σ

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
