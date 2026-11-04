module

public import SerrePositivity.InfinityCategories.Derived.Localization.SimplexAttachmentFamilies
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.CoconeFamilyLastArrow
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalFatDiagram

/-!
概要：元の固定端点 Hom 全族を、指定された全余錐族を保って全線型図式へ延長する。
方針：共有始点を元の区間 Hom の境界条件から証明し、実 attachment の RLP に代入する。
規約：共有経路・頂点条件を追加の入力にせず、元の Hom 全族と指定余錐を保持する。
使われ方：元の商 Hom 比較円柱を、終端で元の商余錐に厳密一致する全余錐円柱へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma intervalMappingFamilyArrow_source {P X : SSet.{u}} {x y : X _⦋0⦌}
    (f : P ⟶ intervalMappingSpace x y) :
    (f ≫ vertexFiberι ((pre (boundary 1).ι).app X)
      (functorVertex (intervalMappingBoundary x y))) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = SSet.const x := by
  have he := intervalMappingUncurry_zero f
  rw [← curry_evaluateFunctorAt_interval] at he
  simpa only [intervalMappingUncurry, curry_uncurry] using he

lemma intervalMappingFamilyArrow_target {P X : SSet.{u}} {x y : X _⦋0⦌}
    (f : P ⟶ intervalMappingSpace x y) :
    (f ≫ vertexFiberι ((pre (boundary 1).ι).app X)
      (functorVertex (intervalMappingBoundary x y))) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = SSet.const y := by
  have he := intervalMappingUncurry_one f
  rw [← curry_evaluateFunctorAt_interval] at he
  simpa only [intervalMappingUncurry, curry_uncurry] using he

/-- 元の固定端点 Hom 全族を指定余錐に沿って延長し、全前段と元の終端辺を保持する。 -/
lemma exists_relative_intervalMappingCoconeFamily {P T X : SSet.{u}} [Quasicategory X]
    {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ X) (z : X _⦋0⦌)
    (j : T ⟶ P) [Mono j]
    (G : T ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj X)
    (f : P ⟶ intervalMappingSpace
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
    (hG : G ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app X =
      SSet.const (functorVertex D))
    (hGe : j ≫ f ≫ vertexFiberι ((pre (boundary 1).ι).app X)
        (functorVertex (intervalMappingBoundary
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)) ≫
        (pre (joinStdSimplexIso 0 0).hom).app X =
      G ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app X) :
    ∃ U : P ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj X,
      j ≫ U = G ∧
      U ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app X = SSet.const (functorVertex D) ∧
      U ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app X =
        f ≫ vertexFiberι ((pre (boundary 1).ι).app X)
          (functorVertex (intervalMappingBoundary
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)) ≫
          (pre (joinStdSimplexIso 0 0).hom).app X ∧
      U ≫ evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z := by
  let N := f ≫ vertexFiberι ((pre (boundary 1).ι).app X)
    (functorVertex (intervalMappingBoundary
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z))
  have hn₀ := intervalMappingFamilyArrow_source f
  have hn₁ := intervalMappingFamilyArrow_target f
  have hp : (simplexLastPoint n).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = stdSimplex.obj₀Equiv.symm (Fin.last n) := by
    have h₀ : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
    rw [h₀, ← SSet.yonedaEquiv_comp, Category.id_comp]
    exact Equiv.apply_symm_apply _ _
  have hl : (SSet.const (functorVertex D) : P ⟶ _) ≫
      (pre (simplexLastPoint n)).app X ≫ (pointFunctorEvaluationIso X).hom =
      SSet.const (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) := by
    change (SSet.const (functorVertex D) : P ⟶ _) ≫
      (pre (simplexLastPoint n)).app X ≫ evaluateFunctorAt
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = _
    rw [stable_pre_evaluateFunctorAt, hp, SSet.const_comp, evaluateFunctorAt_functorVertex]
  have hr : (N ≫ (pre (joinStdSimplexIso 0 0).hom).app X) ≫
      (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app X ≫ (pointFunctorEvaluationIso X).hom =
      N ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    change (N ≫ (pre (joinStdSimplexIso 0 0).hom).app X) ≫
      (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app X ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = _
    rw [Category.assoc, stable_pre_evaluateFunctorAt, stable_pre_evaluateFunctorAt]
    rfl
  have hab : (SSet.const (functorVertex D) : P ⟶ _) ≫ (pre (simplexLastPoint n)).app X =
      (N ≫ (pre (joinStdSimplexIso 0 0).hom).app X) ≫
        (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app X := by
    apply (cancel_mono (pointFunctorEvaluationIso X).hom).mp
    simpa only [Category.assoc] using hl.trans (hr.trans hn₀).symm
  obtain ⟨U, hU, hUp, hUn⟩ := exists_relative_simplexAttachmentFamily n j G
    (SSet.const (functorVertex D)) (N ≫ (pre (joinStdSimplexIso 0 0).hom).app X) hab
    (by rw [SSet.comp_const, hG]) hGe
  refine ⟨U, hU, hUp, hUn, ?_⟩
  exact (spanCoconeFamily_apex_of_lastArrow U N hUn).trans hn₁

end SerrePositivity.KST.LocalizingInvariants
