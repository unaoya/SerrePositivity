module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TriangleCompactCardinals
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallLimitFunctorContinuity

/-!
概要：生成辺・端点・恒等射・三角形の三辺を、一つの compact 保存濃度へ揃える。
方針：三つの公開 Ind 模型の小さい生成族の像を、標的ごとに一つの族へまとめる。
規約：三角形表示用と演算用の別の濃度を同一視しない。
使われ方：HTT 5.5.4.14 の一つの実 Ind 像と三角形全体の同時細分。

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

/-- 実像の演算と三角形表示を、全て同じ正則濃度に揃えられる。 -/
lemma exists_triangleOperationsCompactCardinal (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    (edges : I → C _⦋1⦌) (σ : Cardinal.{u}) :
    ∃ κ μ : Cardinal.{u}, κ.IsRegular ∧ μ.IsRegular ∧ σ < μ ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ C ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ ((ihom (Δ[1] : SSet.{u + 1})).obj C) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ ((ihom (Δ[2] : SSet.{u + 1})).obj C) ∧
      (∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatorArrowVertex edges i)) ∧
      (∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ f → ∀ j : Fin 2,
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j)).app _ f)) ∧
      (∀ x : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ x →
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u + 1}) C).app _ x)) ∧
      ∀ t : ((ihom (Δ[2] : SSet.{u + 1})).obj C) _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ t → ∀ j : Fin 3,
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (((pre (stdSimplex.δ j)).app C).app _ t) := by
  let Ar := (ihom (Δ[1] : SSet.{u + 1})).obj C
  let T := (ihom (Δ[2] : SSet.{u + 1})).obj C
  let B : ULift.{u} (Fin 3) → SSet.{u + 1} := fun i ↦ ![C, Ar, T] i.down
  have (i : ULift.{u} (Fin 3)) : Quasicategory (B i) := by
    rcases i with ⟨i⟩
    fin_cases i <;> dsimp [B, Ar, T] <;> infer_instance
  have hB : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible (B i) := by
    rintro ⟨i⟩
    fin_cases i
    · exact hC.isAccessible
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.arrow_isPresentable hC).isAccessible
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.triangle_isPresentable hC).isAccessible
  obtain ⟨κ, hκ, _, hBκ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_common_accessibilityCardinal B hB σ
  have hCκ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ C := hBκ ⟨0⟩
  have hArκ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ Ar := hBκ ⟨1⟩
  have hTκ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ T := hBκ ⟨2⟩
  have : Fact κ.IsRegular := ⟨hκ⟩
  obtain ⟨AC, hAC, ⟨eC⟩⟩ := hCκ.exists_indEquivalence
  obtain ⟨AA, hAA, ⟨eA⟩⟩ := hArκ.exists_indEquivalence
  obtain ⟨AT, hAT, ⟨eT⟩⟩ := hTκ.exists_indEquivalence
  have := hAC
  have := hAA
  have := hAT
  let iC := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ AC
  let iA := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ AA
  let iT := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ AT
  let gL := eC.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u + 1}) C
  let gE (j : Fin 2) := eA.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j)
  let gT (j : Fin 3) := eT.hom ≫ (pre (stdSimplex.δ j)).app C
  have hL : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ gL :=
    (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits κ eC.isQCatEquivalence).comp
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.constantFunctorMap_preservesSmallColimits _).isKappaAccessibleFunctor κ)
  have hE (j : Fin 2) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (gE j) :=
    (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits κ eA.isQCatEquivalence).comp
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorSmallColimits.evaluateFunctorAt_preservesSmallColimits hC.hasSmallColimits _).isKappaAccessibleFunctor κ)
  have hT (j : Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (gT j) :=
    (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits κ eT.isQCatEquivalence).comp
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.triangleFace_preservesSmallColimits hC.hasSmallColimits j).isKappaAccessibleFunctor κ)
  let vA : AC _⦋0⦌ ⊕ ((Fin 3 × AT _⦋0⦌) ⊕ I) → Ar _⦋0⦌ :=
    Sum.elim (fun a ↦ gL.app _ (iC.app _ (ULift.up a)))
      (Sum.elim (fun a ↦ (gT a.1).app _ (iT.app _ (ULift.up a.2)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatorArrowVertex edges))
  let vC : Fin 2 × AA _⦋0⦌ → C _⦋0⦌ :=
    fun a ↦ (gE a.1).app _ (iA.app _ (ULift.up a.2))
  obtain ⟨ρA, _, hσρ, hvA⟩ := hArκ.isAccessible.exists_common_compactCardinal vA σ
  obtain ⟨ρC, _, _, hvC⟩ := hCκ.isAccessible.exists_common_compactCardinal vC σ
  obtain ⟨μ, hμ, hm, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_regular_cardinalChangeBound κ (max ρA ρC)
  have : Fact μ.IsRegular := ⟨hμ⟩
  have hρA : ρA ≤ μ := (le_max_left _ _).trans hm.le
  have hρC : ρC ≤ μ := (le_max_right _ _).trans hm.le
  refine ⟨κ, μ, hκ, hμ, hσρ.trans_le hρA, hb,
    hCκ.of_cardinalChangeBound hb, hArκ.of_cardinalChangeBound hb,
    hTκ.of_cardinalChangeBound hb,
    (fun j ↦ (hvA (Sum.inr (Sum.inr j))).of_le hρA), ?_, ?_, ?_⟩
  · intro f hf j
    obtain ⟨_, _, _, _, hj⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_imageCompactGenerating_of_cardinalChangeBound hb
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ind_hasSmallKappaFilteredColimits κ AA) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasSmallFixedVertexMaps κ AA)
      iA (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isKappaCompactGenerating κ AA) (gE j) (hE j)
      (fun a ↦ (hvC (j, a)).of_le hρC)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactImages_of_equivalence eA _ hj f hf
  · obtain ⟨_, _, _, _, hj⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_imageCompactGenerating_of_cardinalChangeBound hb
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ind_hasSmallKappaFilteredColimits κ AC) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasSmallFixedVertexMaps κ AC)
      iC (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isKappaCompactGenerating κ AC) gL hL
      (fun a ↦ (hvA (Sum.inl a)).of_le hρA)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactImages_of_equivalence eC _ hj
  · intro t ht j
    obtain ⟨_, _, _, _, hj⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_imageCompactGenerating_of_cardinalChangeBound hb
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ind_hasSmallKappaFilteredColimits κ AT) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasSmallFixedVertexMaps κ AT)
      iT (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isKappaCompactGenerating κ AT) (gT j) (hT j)
      (fun a ↦ (hvA (Sum.inr (Sum.inl (j, a)))).of_le hρA)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactImages_of_equivalence eT _ hj t ht

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
