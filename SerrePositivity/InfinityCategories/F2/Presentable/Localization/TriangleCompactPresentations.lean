module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.TriangleCompactCardinals
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredPosetNerve
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalUniverseLift

/-!
概要：元の各三角形を、三辺が同時に compact な全三角形の filtered poset 表示にする。
方針：公開された小さい compact 生成表示を共終 poset に制限する。
規約：元の三角形の頂点を厳密に保持し、三つの辺の指定余錐の普遍性も返す。
使われ方：HTT 5.5.4.14 の二対三則に向けた同時部分表示の入力。
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
variable {C : SSet.{u + 1}} [Quasicategory C]

/-- 元の全三角形を保つ、三辺も compact な単一の filtered poset 表示。 -/
def HasCompactTrianglePosetPresentation (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (τ : (Δ[2] : SSet.{u + 1}) ⟶ C) : Prop :=
  ∃ (P : Type u) (o : PartialOrder P),
    letI := o
    IsCardinalFiltered P κ ∧ IsKappaFiltered κ (nerve P) ∧
    ∃ (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve P) ⟶
        (ihom (Δ[2] : SSet.{u + 1})).obj C) (c : JoinCocone D),
      c.vertex = functorVertex τ ∧ IsColimitCone c ∧
      (∀ k, Compact.IsKappaCompact.{u, u + 1} κ (D.app _ k)) ∧
      (∀ k (j : Fin 3), Compact.IsKappaCompact.{u, u + 1} κ
        (((pre (stdSimplex.δ j)).app C).app _ (D.app _ k))) ∧
      ∀ j : Fin 3, IsColimitCone (mapJoinCocone ((pre (stdSimplex.δ j)).app C) c) ∧
        (mapJoinCocone ((pre (stdSimplex.δ j)).app C) c).vertex =
          functorVertex (stdSimplex.δ j ≫ τ)

/-- 全三角形の accessibility と三辺の compact 保存から、元の各三角形の同時表示。 -/
lemma triangle_hasCompactPosetPresentation {κ : Cardinal.{u}} [Fact κ.IsRegular]
    (hC : HasSmallColimits C)
    (hT : IsKappaAccessible κ ((ihom (Δ[2] : SSet.{u + 1})).obj C))
    (hfaces : ∀ t : ((ihom (Δ[2] : SSet.{u + 1})).obj C) _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} κ t → ∀ j : Fin 3,
        Compact.IsKappaCompact.{u, u + 1} κ (((pre (stdSimplex.δ j)).app C).app _ t))
    (τ : (Δ[2] : SSet.{u + 1}) ⟶ C) : HasCompactTrianglePosetPresentation κ τ := by
  obtain ⟨A, hA, i, hi⟩ := hT.2.2
  have := hA
  obtain ⟨K, hK, hκK, a, c, hv, hc⟩ := hi.presentation (functorVertex τ)
  have := hK
  have := hκK
  obtain ⟨P, o, f, hP, hN, hf⟩ := Ind.exists_cofinal_kappaFiltered_poset (κ := κ) K
  let := o
  let r := (SSet.uliftFunctor.{u + 1, u}).map f
  let D := r ≫ (SSet.uliftFunctor.{u + 1, u}).map a ≫ i
  let d := c.restrict r
  have hd : IsColimitCone d :=
    (Ind.isColimitCone_iff_restrict_rightCofinal r (Ind.isRightCofinal_ulift f hf) c).mp hc
  have hvd : d.vertex = functorVertex τ := (JoinCocone.vertex_restrict c r).trans hv
  have hcomp : ∀ k, Compact.IsKappaCompact.{u, u + 1} κ (D.app _ k) := by
    rintro ⟨k⟩
    exact hi.compact (a.app _ (f.app _ k))
  refine ⟨P, o, hP, hN, D, d, hvd, hd, hcomp, ?_, ?_⟩
  · intro k j
    exact hfaces _ (hcomp k) j
  · intro j
    refine ⟨triangleFace_preservesSmallColimits hC j _ _ d hd, ?_⟩
    rw [Ind.mapJoinCocone_vertex, hvd]
    rfl

/-- 元の presentable 圏だけから、全三角形を同じ濃度で同時に表示できる。 -/
lemma exists_compactTrianglePosetPresentations (hC : IsPresentable C) (σ : Cardinal.{u}) :
    ∃ (κ : Cardinal.{u}) (hκ : κ.IsRegular),
      letI : Fact κ.IsRegular := ⟨hκ⟩
      σ < κ ∧ ∀ τ : (Δ[2] : SSet.{u + 1}) ⟶ C,
        HasCompactTrianglePosetPresentation κ τ := by
  obtain ⟨_, κ, _, hκ, hσ, _, _, _, hT, hfaces⟩ :=
    exists_triangleFacesCompactCardinal hC σ
  have : Fact κ.IsRegular := ⟨hκ⟩
  exact ⟨κ, hκ, hσ, triangle_hasCompactPosetPresentation hC.hasSmallColimits hT hfaces⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
