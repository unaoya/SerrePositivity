module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSimplexCategoryEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeSimplexMapPullback

/-!
概要：全パラメーターの HA セル評価と、元のセルの面・退化との可換式を示す。
方針：同じ有限射列の各単体と閉零成分の連続引き戻しを比較する。
規約：全射列と全ての単調写像を保持する。
使われ方：3b-3 R6、元の native 余錐セルの族の貼り合わせ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- 全 nerve の HA セル評価は、元の面・退化の全引き戻しに自然である。 -/
@[reassoc]
lemma strictSimplexCategoryEvaluation_pullback (A : Type u) [CommRing A]
    (E : Type (u + 1)) [DGCategory A E] {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) :
    (nerveMap (strictSimplexPullbackFunctor A E α) ▷ (Δ[m] : SSet.{u + 1})) ≫
        strictSimplexCategoryEvaluation A E m =
      (nerve (StrictSimplexCategory A E n) ◁ SSet.stdSimplex.map (SimplexCategory.mkHom α)) ≫
        strictSimplexCategoryEvaluation A E n := by
  apply SSet.hom_ext
  rintro ⟨⟨q⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨d, ⟨τ⟩⟩
  change ((strictSimplexCellFamily A E m).orderedSimplexFamily
      (d ⋙ strictSimplexPullbackFunctor A E α) (ULift.up τ)).diagonal =
    ((strictSimplexCellFamily A E n).orderedSimplexFamily d
      (ULift.up (τ ≫ SimplexCategory.mkHom α))).diagonal
  apply congrArg OrderedSimplexFamily.diagonal
  apply OrderedSimplexFamily.ext
  · intro a
    exact Pullback.pullback_comp (d.obj a).val τ.toOrderHom α
  · intro a b hab
    exact (d.map (homOfLE hab)).pullback_pullback α τ.toOrderHom

/-- 元の native セルの通常関手は、元の面・退化を保つ同じ引き戻しと一致する。 -/
lemma strictBarNativeSimplexFunctor_pullback (A : Type u) [CommRing A]
    (J : Type) [SmallCategory J] {m n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    strictBarNativeSimplexFunctor A J
        (((SSet.uliftFunctor.{u, 0}).obj (nerve J)).map (SimplexCategory.mkHom α).op s) =
      strictBarNativeSimplexFunctor A J s ⋙
        strictSimplexPullbackFunctor A (RightModule A PUnit.{1}) (extendOrderHom α) := by
  apply CategoryTheory.Functor.hext
  · intro F
    exact congrArg (fun t : Simplex A (RightModule A PUnit.{1}) (m + 1) =>
        (⟨t⟩ : StrictSimplexCategory A (RightModule A PUnit.{1}) (m + 1)))
      (dgCoherentBarNativeSimplex_map A PUnit.{1} (smallStrictBarDiagram A F)
        (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)) s α)
  · intro F G η
    exact strictBarNativeSimplexMap_pullback A J η s α

/-- 元の native 余錐セルの全パラメーターを同時に評価する。 -/
def strictBarNativeCellEvaluation (A : Type u) [CommRing A] (J : Type) [SmallCategory J]
    {n : ℕ} (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    nerve (J ⥤ ModuleCategory A PUnit.{1}) ⊗ (Δ[n + 1] : SSet.{u + 1}) ⟶
      dgNerve A (RightModule A PUnit.{1}) :=
  (nerveMap (strictBarNativeSimplexFunctor A J s) ▷ (Δ[n + 1] : SSet.{u + 1})) ≫
    strictSimplexCategoryEvaluation A (RightModule A PUnit.{1}) (n + 1)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
