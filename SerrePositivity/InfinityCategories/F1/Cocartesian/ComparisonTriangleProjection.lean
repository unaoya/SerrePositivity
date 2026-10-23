module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.Functor
public import SerrePositivity.InfinityCategories.F1.Fibrations.InvertibleCartesian
public import SerrePositivity.InfinityCategories.F1.Categories.CoreFaces
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianCancellation
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：同じ始点と底の辺を持つ cocartesian 辺を、可逆な後半辺の三角形で比較する。
方針：零番目の二次ホーンを持ち上げ、三角形の消去と底での退化辺を使う。
規約：元の三角形・両辺と底への退化射影を厳密に保持する。
使われ方：選んだ水平 lift の保存から、全 cocartesian 辺の保存を導く。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ始点と底の辺を持つ二つの cocartesian 辺は可逆な後半辺の三角形を持つ。 -/
lemma exists_cocartesianComparisonTriangle_over {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [InnerFibration p]
    (e h : E _⦋1⦌) (he : IsCocartesianEdge p e) (hh : IsCocartesianEdge p h)
    (hs : E.δ 1 h = E.δ 1 e) (hp : p.app (Opposite.op ⦋1⦌) h = p.app _ e) :
    ∃ t : (Δ[2] : SSet.{u}) ⟶ E,
      t ≫ p = stdSimplex.σ 1 ≫ SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋1⦌) e) ∧
      stdSimplex.δ 2 ≫ t = SSet.yonedaEquiv.symm h ∧
      stdSimplex.δ 1 ≫ t = SSet.yonedaEquiv.symm e ∧
      IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv (stdSimplex.δ 0 ≫ t))) := by
  obtain ⟨a, ha₂, ha₁⟩ := horn₂₀.isPushout.exists_desc
    (SSet.yonedaEquiv.symm h) (SSet.yonedaEquiv.symm e) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm, hs])
  let b : (Δ[2] : SSet.{u}) ⟶ B :=
    stdSimplex.σ 1 ≫ SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋1⦌) e)
  have hb (i : Fin 3) (hi : i = 1 ∨ i = 2) :
      stdSimplex.δ i ≫ b = SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋1⦌) e) := by
    have hδ : (stdSimplex.δ i : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫ stdSimplex.σ 1 = 𝟙 _ := by
      rcases hi with rfl | rfl <;> apply SSet.yonedaEquiv.injective <;> decide
    change stdSimplex.δ i ≫ (stdSimplex.σ 1 ≫ _) = _
    rw [← Category.assoc, hδ, Category.id_comp]
  have sq : CommSq a (horn 2 0).ι p b := by
    constructor
    apply horn₂₀.isPushout.hom_ext
    · simp only [← Category.assoc, ha₂, horn.ι_ι]
      rw [hb 2 (Or.inr rfl), SSet.yonedaEquiv_symm_comp, hp]
    · simp only [← Category.assoc, ha₁, horn.ι_ι]
      rw [hb 1 (Or.inl rfl), SSet.yonedaEquiv_symm_comp]
  have hai : a.app (Opposite.op ⦋1⦌) (initialHornEdge 0) = h := by
    have ht := congrArg SSet.yonedaEquiv ha₂
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at ht
    have hi : SSet.yonedaEquiv horn₂₀.ι₀₁ = initialHornEdge 0 := by
      apply Subtype.ext
      apply stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    rwa [hi] at ht
  have := hh 0 a b hai sq
  let t := sq.lift
  have ht₂ : stdSimplex.δ 2 ≫ t = SSet.yonedaEquiv.symm h := by
    rw [← horn.ι_ι_assoc 0 2 (by decide), sq.fac_left]
    exact ha₂
  have ht₁ : stdSimplex.δ 1 ≫ t = SSet.yonedaEquiv.symm e := by
    rw [← horn.ι_ι_assoc 0 1 (by decide), sq.fac_left]
    exact ha₁
  refine ⟨t, sq.fac_right, ht₂, ht₁, ?_⟩
  have hc : IsCocartesianEdge p (SSet.yonedaEquiv (stdSimplex.δ 0 ≫ t)) := by
    apply kanIsCocartesianEdge_triangle_second_of_first_long t p
    · rw [ht₂, Equiv.apply_symm_apply]; exact hh
    · rw [ht₁, Equiv.apply_symm_apply]; exact he
  apply isInvertibleEdge_of_isCocartesianEdge p _ hc
  apply (isInvertibleEdge_congr
    (e := (edgeOfSimplex (SSet.yonedaEquiv (stdSimplex.δ 0 ≫ t))).map ((truncation 2).map p))
    (f := edgeOfSimplex (SSet.yonedaEquiv (stdSimplex.δ 0 ≫ b))) ?_).mpr
  · have hδ : SimplexCategory.δ (0 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) =
        SimplexCategory.const ⦋1⦌ ⦋1⦌ 1 := by decide
    change IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv
      (stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) ≫
        (stdSimplex.map (SimplexCategory.σ (1 : Fin 2)) ≫
          SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋1⦌) e)))))
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hδ,
      ← SSet.yonedaEquiv_naturality, Equiv.apply_symm_apply]
    exact isInvertibleEdge_map_const _ 1
  · change p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (stdSimplex.δ 0 ≫ t)) =
      SSet.yonedaEquiv (stdSimplex.δ 0 ≫ b)
    rw [← SSet.yonedaEquiv_comp, Category.assoc, sq.fac_right]

end SerrePositivity.InfinityCategories
