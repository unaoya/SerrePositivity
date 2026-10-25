module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.TriangleFaces
public import SerrePositivity.InfinityCategories.F2.Presentable.StrongCompactCardinals

/-!
概要：三角形の全 compact 対象の三辺が同時に compact となる共通濃度を構成する。
方針：公開 Ind 模型の小さい生成族の三つの像を一つの族にまとめて濃度変更する。
規約：三つの辺ごとに濃度を上げず、全三角形の同じ濃度を保持する。
使われ方：HTT 5.5.4.14 の二対三則に向けた、三辺を保つ全関手圏の表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
variable {C : SSet.{u + 1}} [Quasicategory C]

/-- 元の圏・射圏・三角形圏が同じ濃度で accessible となり、三辺の制限は compact 保存。 -/
lemma exists_triangleFacesCompactCardinal (hC : IsPresentable C) (σ : Cardinal.{u}) :
    ∃ κ μ : Cardinal.{u}, κ.IsRegular ∧ μ.IsRegular ∧ σ < μ ∧
      IsCardinalChangeBound κ μ ∧ IsKappaAccessible μ C ∧
      IsKappaAccessible μ ((ihom (Δ[1] : SSet.{u + 1})).obj C) ∧
      IsKappaAccessible μ ((ihom (Δ[2] : SSet.{u + 1})).obj C) ∧
      ∀ (t : ((ihom (Δ[2] : SSet.{u + 1})).obj C) _⦋0⦌),
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
  obtain ⟨A, hA, ⟨e⟩⟩ := hTκ.exists_indEquivalence
  have := hA
  let i := Ind.indYoneda κ A
  let g (j : Fin 3) := e.hom ≫ (pre (stdSimplex.δ j)).app C
  have hg (j : Fin 3) : IsKappaAccessibleFunctor κ (g j) :=
    (equivalence_preservesSmallKappaFilteredColimits κ e.isQCatEquivalence).comp
      ((triangleFace_preservesSmallColimits hC.hasSmallColimits j).isKappaAccessibleFunctor κ)
  let v : Fin 3 × A _⦋0⦌ → Ar _⦋0⦌ :=
    fun a ↦ (g a.1).app _ (i.app _ (ULift.up a.2))
  obtain ⟨ρ, _, hσρ, hv⟩ := hArκ.isAccessible.exists_common_compactCardinal v σ
  obtain ⟨μ, hμ, hρμ, hb⟩ := exists_regular_cardinalChangeBound κ ρ
  have : Fact μ.IsRegular := ⟨hμ⟩
  refine ⟨κ, μ, hκ, hμ, hσρ.trans hρμ, hb,
    hCκ.of_cardinalChangeBound hb, hArκ.of_cardinalChangeBound hb,
    hTκ.of_cardinalChangeBound hb, ?_⟩
  intro t ht j
  obtain ⟨_, _, _, _, hj⟩ := exists_imageCompactGenerating_of_cardinalChangeBound hb
    (Ind.ind_hasSmallKappaFilteredColimits κ A) (Ind.ind_hasSmallFixedVertexMaps κ A)
    i (indYoneda_isKappaCompactGenerating κ A) (g j) (hg j)
    (fun a ↦ (hv (j, a)).of_le hρμ.le)
  exact compactImages_of_equivalence e ((pre (stdSimplex.δ j)).app C) hj t ht

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
