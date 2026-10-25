module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.SeededAlternatingStage
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.FixedSourceExtension

/-!
概要：固定小図式を保持する相対交互構成の全余錐を選ぶ。
方針：固定入力を含む join 図式の compact 性を使って同じ表示内へ相対因子化する。
規約：元の入力図式の余極限を要求しない。
使われ方：入力付き相対交互塔の実際の一段延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：入力付き厳密前置段には指定成分の同じ表示内での延長余錐がある。
方針：入力と元の前置段の compact 性を全 join 図式の相対因子化へ渡す。
規約：入力の全単体と元の表示添字を保持する。
使われ方：入力付き閉前置段を構成する具体的全余錐。 -/
lemma exists_seededAlternatingCocone
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ)
    {A K : SSet.{u}} [Quasicategory A] [Quasicategory K] (hK : IsKappaSmall μ K)
    {x : (Δ[0] : SSet.{u + 1}) ⟶ Ind.IndInfinity μ A}
    {I : Fin 2 → SSet.{u}} [∀ c, Quasicategory (I c)] [∀ c, IsKappaFiltered μ (I c)]
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ sliceOver x}
    {z : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ sliceOver x}
    (hz : ∀ v : K _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((z ≫ sliceOverProjection x).app (Opposite.op ⦋0⦌) (ULift.up v)))
    (hP : ∀ c, ∀ v : (I c) _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((P c ≫ sliceOverProjection x).app (Opposite.op ⦋0⦌) (ULift.up v)))
    (hcol : ∀ c, IsColimitCone (sliceDiagramCocone (P c)))
    {a : AlternatingIndex κ}
    (s : SeededAlternatingOpenStage (κ := κ) (I := I) (P := P) z a) (c : Fin 2) :
    ∃ j : JoinCocone (s.stage.index c), ∃ d : JoinCocone s.under,
      joinMap ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (alternatingLowerSection κ a c))) (𝟙 Δ[0]) ≫
        d.val ≫ sliceUnderProjection z =
      (((uliftSliceUnderIso.{u, u + 1} (s.stage.index c)).hom.app (Opposite.op ⦋0⦌))
        (ULift.up j)).val ≫ P c := by
  have hμ : Cardinal.aleph0 < μ :=
    (Cardinal.IsRegular.aleph0_le (Fact.out : κ.IsRegular)).trans_lt h.1
  have hR : ∀ v : (nerve (AlternatingLower κ a)) _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} μ
        ((s.under ≫ sliceUnderProjection z ≫ sliceOverProjection x).app
          (Opposite.op ⦋0⦌) (ULift.up v)) := by
    intro v
    rw [← Category.assoc s.under, s.projection]
    exact s.stage.vertex_isKappaCompact hP v
  have hi : (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (alternatingLowerSection κ a c)) ≫ s.under ≫ sliceUnderProjection z =
      (SSet.uliftFunctor.{u + 1, u}).map (s.stage.index c) ≫ P c := by
    rw [s.projection]
    exact s.stage.component_eq c
  obtain ⟨t⟩ := exists_fixedSourceFactorization hμ
    (alternatingComponentLower_isKappaSmall h a c) hK (alternatingLower_isKappaSmall h a)
    s.under (s.stage.index c) (nerveMap (alternatingLowerSection κ a c)) (P c)
    hz hR (hcol c) hi
  exact ⟨t.index, fixedSourceFactorizationCocone t, fixedSourceFactorizationCocone_component t⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
