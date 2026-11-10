module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.TriangleCompactCardinals
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallLimitFunctorContinuity

/-!
概要：生成辺・端点・恒等射・三角形の三辺を、一つの compact 保存濃度へ揃える。
方針：三つの公開 Ind 模型の小さい生成族の像を、標的ごとに一つの族へまとめる。
規約：三角形表示用と演算用の別の濃度を同一視しない。
使われ方：HTT 5.5.4.14 の一つの実 Ind 像と三角形全体の同時細分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 実像の演算と三角形表示を、全て同じ正則濃度に揃えられる。 -/
lemma exists_triangleOperationsCompactCardinal (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    (edges : I → C _⦋1⦌) (σ : Cardinal.{u}) :
    ∃ κ μ : Cardinal.{u}, κ.IsRegular ∧ μ.IsRegular ∧ σ < μ ∧
      IsCardinalChangeBound κ μ ∧ IsKappaAccessible μ C ∧
      IsKappaAccessible μ ((ihom (Δ[1] : SSet.{u + 1})).obj C) ∧
      IsKappaAccessible μ ((ihom (Δ[2] : SSet.{u + 1})).obj C) ∧
      (∀ i, Compact.IsKappaCompact.{u, u + 1} μ (generatorArrowVertex edges i)) ∧
      (∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
        Compact.IsKappaCompact.{u, u + 1} μ f → ∀ j : Fin 2,
          Compact.IsKappaCompact.{u, u + 1} μ
            ((evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j)).app _ f)) ∧
      (∀ x : C _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ x →
        Compact.IsKappaCompact.{u, u + 1} μ
          ((constantFunctorMap (Δ[1] : SSet.{u + 1}) C).app _ x)) ∧
      ∀ t : ((ihom (Δ[2] : SSet.{u + 1})).obj C) _⦋0⦌,
        Compact.IsKappaCompact.{u, u + 1} μ t → ∀ j : Fin 3,
          Compact.IsKappaCompact.{u, u + 1} μ (((pre (stdSimplex.δ j)).app C).app _ t) := by
  let Ar := (ihom (Δ[1] : SSet.{u + 1})).obj C
  let T := (ihom (Δ[2] : SSet.{u + 1})).obj C
  let B : ULift.{u} (Fin 3) → SSet.{u + 1} := fun i ↦ ![C, Ar, T] i.down
  have (i : ULift.{u} (Fin 3)) : Quasicategory (B i) := by
    rcases i with ⟨i⟩
    fin_cases i <;> dsimp [B, Ar, T] <;> infer_instance
  have hB : ∀ i, IsAccessible (B i) := by
    rintro ⟨i⟩
    fin_cases i
    · exact hC.isAccessible
    · exact (arrow_isPresentable hC).isAccessible
    · exact (triangle_isPresentable hC).isAccessible
  obtain ⟨κ, hκ, _, hBκ⟩ := exists_common_accessibilityCardinal B hB σ
  have hCκ : IsKappaAccessible κ C := hBκ ⟨0⟩
  have hArκ : IsKappaAccessible κ Ar := hBκ ⟨1⟩
  have hTκ : IsKappaAccessible κ T := hBκ ⟨2⟩
  have : Fact κ.IsRegular := ⟨hκ⟩
  obtain ⟨AC, hAC, ⟨eC⟩⟩ := hCκ.exists_indEquivalence
  obtain ⟨AA, hAA, ⟨eA⟩⟩ := hArκ.exists_indEquivalence
  obtain ⟨AT, hAT, ⟨eT⟩⟩ := hTκ.exists_indEquivalence
  have := hAC
  have := hAA
  have := hAT
  let iC := Ind.indYoneda κ AC
  let iA := Ind.indYoneda κ AA
  let iT := Ind.indYoneda κ AT
  let gL := eC.hom ≫ constantFunctorMap (Δ[1] : SSet.{u + 1}) C
  let gE (j : Fin 2) := eA.hom ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j)
  let gT (j : Fin 3) := eT.hom ≫ (pre (stdSimplex.δ j)).app C
  have hL : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ gL :=
    (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits κ eC.isQCatEquivalence).comp
      ((constantFunctorMap_preservesSmallColimits _).isKappaAccessibleFunctor κ)
  have hE (j : Fin 2) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (gE j) :=
    (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits κ eA.isQCatEquivalence).comp
      ((evaluateFunctorAt_preservesSmallColimits hC.hasSmallColimits _).isKappaAccessibleFunctor κ)
  have hT (j : Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (gT j) :=
    (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits κ eT.isQCatEquivalence).comp
      ((triangleFace_preservesSmallColimits hC.hasSmallColimits j).isKappaAccessibleFunctor κ)
  let vA : AC _⦋0⦌ ⊕ ((Fin 3 × AT _⦋0⦌) ⊕ I) → Ar _⦋0⦌ :=
    Sum.elim (fun a ↦ gL.app _ (iC.app _ (ULift.up a)))
      (Sum.elim (fun a ↦ (gT a.1).app _ (iT.app _ (ULift.up a.2)))
        (generatorArrowVertex edges))
  let vC : Fin 2 × AA _⦋0⦌ → C _⦋0⦌ :=
    fun a ↦ (gE a.1).app _ (iA.app _ (ULift.up a.2))
  obtain ⟨ρA, _, hσρ, hvA⟩ := hArκ.isAccessible.exists_common_compactCardinal vA σ
  obtain ⟨ρC, _, _, hvC⟩ := hCκ.isAccessible.exists_common_compactCardinal vC σ
  obtain ⟨μ, hμ, hm, hb⟩ := exists_regular_cardinalChangeBound κ (max ρA ρC)
  have : Fact μ.IsRegular := ⟨hμ⟩
  have hρA : ρA ≤ μ := (le_max_left _ _).trans hm.le
  have hρC : ρC ≤ μ := (le_max_right _ _).trans hm.le
  refine ⟨κ, μ, hκ, hμ, hσρ.trans_le hρA, hb,
    hCκ.of_cardinalChangeBound hb, hArκ.of_cardinalChangeBound hb,
    hTκ.of_cardinalChangeBound hb,
    (fun j ↦ (hvA (Sum.inr (Sum.inr j))).of_le hρA), ?_, ?_, ?_⟩
  · intro f hf j
    obtain ⟨_, _, _, _, hj⟩ := exists_imageCompactGenerating_of_cardinalChangeBound hb
      (Ind.ind_hasSmallKappaFilteredColimits κ AA) (Ind.ind_hasSmallFixedVertexMaps κ AA)
      iA (indYoneda_isKappaCompactGenerating κ AA) (gE j) (hE j)
      (fun a ↦ (hvC (j, a)).of_le hρC)
    exact compactImages_of_equivalence eA _ hj f hf
  · obtain ⟨_, _, _, _, hj⟩ := exists_imageCompactGenerating_of_cardinalChangeBound hb
      (Ind.ind_hasSmallKappaFilteredColimits κ AC) (Ind.ind_hasSmallFixedVertexMaps κ AC)
      iC (indYoneda_isKappaCompactGenerating κ AC) gL hL
      (fun a ↦ (hvA (Sum.inl a)).of_le hρA)
    exact compactImages_of_equivalence eC _ hj
  · intro t ht j
    obtain ⟨_, _, _, _, hj⟩ := exists_imageCompactGenerating_of_cardinalChangeBound hb
      (Ind.ind_hasSmallKappaFilteredColimits κ AT) (Ind.ind_hasSmallFixedVertexMaps κ AT)
      iT (indYoneda_isKappaCompactGenerating κ AT) (gT j) (hT j)
      (fun a ↦ (hvA (Sum.inr (Sum.inl (j, a)))).of_le hρA)
    exact compactImages_of_equivalence eT _ hj t ht

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
