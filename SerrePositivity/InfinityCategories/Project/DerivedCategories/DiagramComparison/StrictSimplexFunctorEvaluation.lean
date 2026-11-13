module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeCellFront

/-!
概要：固定 HA セルへの通常関手の全族評価を、セルの引き戻しと前面の比較へ接続する。
方針：全 nerve の評価の自然性と、元のセル関手の厳密等号を使う。
規約：元の全射列・全 HA 成分の比較である。
使われ方：3b-3 R6、native セルの族の貼り合わせ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (E : Type (u + 1)) [DGCategory A E]
  {C : Type (u + 1)} [Category.{u} C]

/-- 元の HA セルへの通常関手を全パラメーターで同時に評価する。 -/
def strictSimplexFunctorEvaluation {n : ℕ} (F : C ⥤ StrictSimplexCategory A E n) :
    nerve C ⊗ (Δ[n] : SSet.{u + 1}) ⟶ dgNerve A E :=
  (nerveMap F ▷ (Δ[n] : SSet.{u + 1})) ≫ strictSimplexCategoryEvaluation A E n

/-- 同じ全族評価は、元のセルの全面・退化の引き戻しに自然である。 -/
lemma strictSimplexFunctorEvaluation_pullback {m n : ℕ}
    (F : C ⥤ StrictSimplexCategory A E n) (α : Fin (m + 1) →o Fin (n + 1)) :
    strictSimplexFunctorEvaluation A E (F ⋙ strictSimplexPullbackFunctor A E α) =
      (nerve C ◁ SSet.stdSimplex.map (SimplexCategory.mkHom α)) ≫
        strictSimplexFunctorEvaluation A E F := by
  unfold strictSimplexFunctorEvaluation
  have hc : nerveMap (F ⋙ strictSimplexPullbackFunctor A E α) =
      nerveMap F ≫ nerveMap (strictSimplexPullbackFunctor A E α) := rfl
  rw [hc, comp_whiskerRight, Category.assoc, strictSimplexCategoryEvaluation_pullback]
  exact (whisker_exchange_assoc _ _ _).symm

variable (J : Type) [SmallCategory J]

/-- 元の native 余錐セルの全族は、apex を保つ全面・退化に自然である。 -/
lemma strictBarNativeCellEvaluation_pullback {m n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    strictBarNativeCellEvaluation A J
        (((SSet.uliftFunctor.{u, 0}).obj (nerve J)).map (SimplexCategory.mkHom α).op s) =
      (nerve (J ⥤ ModuleCategory A PUnit.{1}) ◁
        SSet.stdSimplex.map (SimplexCategory.mkHom (extendOrderHom α))) ≫
          strictBarNativeCellEvaluation A J s := by
  change strictSimplexFunctorEvaluation A (RightModule A PUnit.{1})
      (strictBarNativeSimplexFunctor A J _) = _
  rw [strictBarNativeSimplexFunctor_pullback, strictSimplexFunctorEvaluation_pullback]
  rfl

/-- 元の native 余錐セルの前面は、元の strict 図式の同じセルの全族評価。 -/
lemma strictBarNativeCellEvaluation_front {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    (nerve (J ⥤ ModuleCategory A PUnit.{1}) ◁
        SSet.stdSimplex.map (SimplexCategory.mkHom Fin.castSuccOrderEmb.toOrderHom)) ≫
      strictBarNativeCellEvaluation A J s =
    (nerve (J ⥤ ModuleCategory A PUnit.{1}) ◁
      (SSet.yonedaEquiv.symm (ULift.up s) : (Δ[n] : SSet.{u + 1}) ⟶
        (SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J)))) ≫
      (strictModuleCoherentFamily A J (𝟭 (J ⥤ ModuleCategory A PUnit.{1}))).evaluation := by
  change _ ≫ strictSimplexFunctorEvaluation A (RightModule A PUnit.{1})
    (strictBarNativeSimplexFunctor A J s) = _
  rw [← strictSimplexFunctorEvaluation_pullback, strictBarNativeSimplexFunctor_front]
  exact (strictModuleCoherentFamily A J (𝟭 (J ⥤ ModuleCategory A PUnit.{1}))).cellEvaluation s

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
