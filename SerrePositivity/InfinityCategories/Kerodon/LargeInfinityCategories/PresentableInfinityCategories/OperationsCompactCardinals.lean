module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.EndpointCompactCardinals
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallLimitFunctorContinuity

/-!
概要：二つの端点評価と恒等射図式を、同じ濃度で compact 保存にする。
方針：二つの実 Ind 模型の小さい生成族の像を先に揃え、公開された像生成定理を三回適用。
規約：関手ごとに別々に濃度を上げて、既得の compact 保存を失わない。
使われ方：Ind 像に全恒等射を入れ、辺クラスの pushout 保存を組み立てる。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 生成射・全候補の端点・全 compact 対象の恒等射を同じ正則濃度で compact にする。 -/
lemma exists_operationsCompactArrowCardinal (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    (edges : I → C _⦋1⦌) (σ : Cardinal.{u}) :
    ∃ κ μ : Cardinal.{u}, κ.IsRegular ∧ μ.IsRegular ∧ σ < μ ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ C ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ ((ihom (Δ[1] : SSet.{u + 1})).obj C) ∧
      (∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatorArrowVertex edges i)) ∧
      (∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ f → ∀ j : Fin 2,
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j)).app _ f)) ∧
      ∀ x : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ x →
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u + 1}) C).app _ x) := by
  let Ar := (ihom (Δ[1] : SSet.{u + 1})).obj C
  obtain ⟨κ, hκ, _, hCκ, hArκ, hgen, _⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_regular_generatorArrowCardinal hC edges σ
  have : Fact κ.IsRegular := ⟨hκ⟩
  obtain ⟨AC, hAC, ⟨eC⟩⟩ := hCκ.exists_indEquivalence
  obtain ⟨AA, hAA, ⟨eA⟩⟩ := hArκ.exists_indEquivalence
  have := hAC
  have := hAA
  let p : Ar ⟶ C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)
  let q : Ar ⟶ C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1)
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u + 1}) C
  let iA := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ AA
  let iC := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ AC
  let gp := eA.hom ≫ p
  let gq := eA.hom ≫ q
  let gL := eC.hom ≫ L
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ gp :=
    (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits κ eA.isQCatEquivalence).comp
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorSmallColimits.evaluateFunctorAt_preservesSmallColimits hC.hasSmallColimits _).isKappaAccessibleFunctor κ)
  have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ gq :=
    (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits κ eA.isQCatEquivalence).comp
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorSmallColimits.evaluateFunctorAt_preservesSmallColimits hC.hasSmallColimits _).isKappaAccessibleFunctor κ)
  have hL : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ gL :=
    (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits κ eC.isQCatEquivalence).comp
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.constantFunctorMap_preservesSmallColimits _).isKappaAccessibleFunctor κ)
  let v : AA _⦋0⦌ ⊕ AA _⦋0⦌ → C _⦋0⦌ := Sum.elim
    (fun a ↦ gp.app _ (iA.app _ (ULift.up a)))
    (fun a ↦ gq.app _ (iA.app _ (ULift.up a)))
  obtain ⟨ρC, _, _, hv⟩ := hC.isAccessible.exists_common_compactCardinal v σ
  obtain ⟨ρA, _, _, hvl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.arrow_isPresentable hC).isAccessible.exists_common_compactCardinal
    (fun a : AC _⦋0⦌ ↦ gL.app _ (iC.app _ (ULift.up a))) σ
  obtain ⟨μ, hμ, hm, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_regular_cardinalChangeBound κ (max σ (max ρC ρA))
  have : Fact μ.IsRegular := ⟨hμ⟩
  have hσ : σ < μ := lt_of_le_of_lt (le_max_left _ _) hm
  have hρC : ρC ≤ μ := ((le_max_left ρC ρA).trans (le_max_right σ _)).trans hm.le
  have hρA : ρA ≤ μ := ((le_max_right ρC ρA).trans (le_max_right σ _)).trans hm.le
  obtain ⟨_, _, _, _, hpc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_imageCompactGenerating_of_cardinalChangeBound hb
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ind_hasSmallKappaFilteredColimits κ AA) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasSmallFixedVertexMaps κ AA)
    iA (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isKappaCompactGenerating κ AA) gp hp
    (fun a ↦ (hv (Sum.inl a)).of_le hρC)
  obtain ⟨_, _, _, _, hqc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_imageCompactGenerating_of_cardinalChangeBound hb
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ind_hasSmallKappaFilteredColimits κ AA) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasSmallFixedVertexMaps κ AA)
    iA (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isKappaCompactGenerating κ AA) gq hq
    (fun a ↦ (hv (Sum.inr a)).of_le hρC)
  obtain ⟨_, _, _, _, hLc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_imageCompactGenerating_of_cardinalChangeBound hb
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ind_hasSmallKappaFilteredColimits κ AC) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasSmallFixedVertexMaps κ AC)
    iC (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isKappaCompactGenerating κ AC) gL hL
    (fun a ↦ (hvl a).of_le hρA)
  refine ⟨κ, μ, hκ, hμ, hσ, hb, hCκ.of_cardinalChangeBound hb,
    hArκ.of_cardinalChangeBound hb, fun i ↦ (hgen i).of_le hb.le, ?_,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactImages_of_equivalence eC L hLc⟩
  intro f hf j
  fin_cases j
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactImages_of_equivalence eA p hpc f hf
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactImages_of_equivalence eA q hqc f hf

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
