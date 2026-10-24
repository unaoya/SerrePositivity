module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationExtensionInvariant
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationTargetFamily
public import SerrePositivity.InfinityCategories.F1.Universe.CoconeShapeNaturality
/-!
概要：補間領域の共同余錐で終点拡張を選び直し、旧族と同じ全終点面を回収する。
方針：元の両境界を余錐の制限で保ち、形状同型の終点面と宇宙自然性を使う。
規約：元の slice 円柱と旧族を変更しない。
使われ方：終点評価下の指定変換を持つ補間全族の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
  (V : IndArrowInterpolationData κ D q)
/-- 概要：元の終点拡張を同じ補間領域へ制限する。
方針：元の包含を前合成する。規約：元の全射を保持。使われ方：終点評価の相対余錐。 -/
def indArrowInterpolationCornerFamily :=
  (SSet.uliftFunctor.{u + 1, u}).map (arrowInterpolationCornerInclusion A) ≫ V.extension
/-- 概要：補間領域の旧終点族は、元の旧族の終点評価そのもの。
方針：全族の終点評価を回収する。規約：元の全射を保持。使われ方：終点評価の相対余錐。 -/
lemma indArrowInterpolationCornerFamily_target :
    (SSet.uliftFunctor.{u + 1, u}).map (arrowInterpolationTargetInclusion A) ≫
      indArrowInterpolationCornerFamily V =
    indArrowInterpolationOldFamily V ≫
      diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  rw [indArrowInterpolationOldFamily, Category.assoc, indArrowInterpolationCommaFamily_target]
  rw [indArrowInterpolationCornerFamily, ← Category.assoc, ← Functor.map_comp,
    arrowInterpolationTargetInclusion_comp, Functor.map_comp, Category.assoc]
variable (c : JoinCocone (indArrowInterpolationCornerFamily V))
/-- 概要：同じ補間領域の余錐から、元の両境界を保つ終点拡張を選ぶ。
方針：元の余錐を全円柱へ戻す。規約：元の全射を保持。使われ方：終点評価の相対余錐。 -/
def IndArrowInterpolationData.withCornerCocone : IndArrowInterpolationData κ D q :=
  V.withExtension (arrowInterpolationExtend c) (by
    have h := congrArg (fun f => (SSet.uliftFunctor.{u + 1, u}).map
      (pushout.inl SSet.ι₀ (joinInl A (Δ[0] : SSet.{u}))) ≫ f)
      (arrowInterpolationExtend_inclusion c)
    simpa only [indArrowInterpolationCornerFamily, ← Category.assoc, ← Functor.map_comp,
      arrowInterpolationCornerInclusion_old] using h) (by
    have h := congrArg (fun f => (SSet.uliftFunctor.{u + 1, u}).map
      (pushout.inr SSet.ι₀ (joinInl A (Δ[0] : SSet.{u}))) ≫ f)
      (arrowInterpolationExtend_inclusion c)
    simpa only [indArrowInterpolationCornerFamily, ← Category.assoc, ← Functor.map_comp,
      arrowInterpolationCornerInclusion_source] using h)
/-- 概要：共同余錐で拡張を選び直しても、元の旧族は変わらない。
方針：同じ slice 円柱の不変性を使う。規約：元の全射を保持。使われ方：終点評価の相対余錐。 -/
lemma indArrowInterpolationOldFamily_withCornerCocone :
    indArrowInterpolationOldFamily (V.withCornerCocone c) = indArrowInterpolationOldFamily V :=
  indArrowInterpolationOldFamily_withExtension _ _ _ _
/-- 概要：選び直した全族の終点評価は、共同余錐の旧終点族への制限。
方針：形状同型と宇宙自然性を使う。規約：元の全射を保持。使われ方：終点評価の相対余錐。 -/
lemma indArrowInterpolationCornerCocone_target :
    indArrowInterpolationCommaFamily (V.withCornerCocone c) ≫
      diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
    (uliftCoconeShapeIso.{u, u + 1} A 0).hom ≫
      joinMap ((SSet.uliftFunctor.{u + 1, u}).map (arrowInterpolationTargetInclusion A))
        (𝟙 (Δ[0] : SSet.{u + 1})) ≫ c.val := by
  rw [indArrowInterpolationCommaFamily_target]
  change (SSet.uliftFunctor.{u + 1, u}).map SSet.ι₁ ≫ arrowInterpolationExtend c = _
  rw [arrowInterpolationExtend, ← Category.assoc, ← Functor.map_comp,
    arrowInterpolationCoconeIso_inv_target]
  have h := congrArg (fun f => f ≫ c.val)
    (uliftCoconeShapeIso_hom_naturality (arrowInterpolationTargetInclusion A) 0)
  simpa only [Category.assoc] using h
end SerrePositivity.InfinityCategories.F2.Ind
