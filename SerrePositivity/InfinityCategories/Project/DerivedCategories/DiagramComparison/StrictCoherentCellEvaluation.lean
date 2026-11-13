module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSimplexEvaluationNaturality

/-!
概要：全 HA 族の元の一つのセルを、その全パラメーターの通常関手として評価する。
方針：元のセルの関手を作り、全有限射列の評価を元の図式の制限と照合する。
規約：全族の自然性と元の各セルの成分を結論で比較する。
使われ方：3b-3 R6、native 余錐の前面と元の図式の全族の一致。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
namespace StrictCoherentFamily
variable {A : Type u} [CommRing A] {E : Type (u + 1)} [DGCategory A E]
  {I : SSet.{u}} {C : Type (u + 1)} [Category.{u} C]

/-- 同じ一つの元のセルで全パラメーターを評価する通常関手。 -/
def cellFunctor (F : StrictCoherentFamily A E I C) {n : ℕ} (s : I _⦋n⦌) :
    C ⥤ StrictSimplexCategory A E n where
  obj c := ⟨coherentDiagramSimplex (F.obj c) s⟩
  map f := F.map f s
  map_id c := F.map_id c s
  map_comp f g := F.map_comp f g s

/-- 元のセルの通常関手は、同じ面・退化による引き戻しと一致する。 -/
lemma cellFunctor_pullback (F : StrictCoherentFamily A E I C) {m n : ℕ}
    (s : I _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1)) :
    F.cellFunctor (I.map (SimplexCategory.mkHom α).op s) =
      F.cellFunctor s ⋙ strictSimplexPullbackFunctor A E α := by
  apply CategoryTheory.Functor.hext
  · intro c
    exact congrArg (fun t : Simplex A E m => (⟨t⟩ : StrictSimplexCategory A E m))
      (coherentDiagramSimplex_map (F.obj c) α s)
  · intro c d f
    exact F.map_pullback f α s

/-- セルの全パラメーター評価は、元の全族の同じ Yoneda 制限と一致する。 -/
@[reassoc]
lemma cellEvaluation (F : StrictCoherentFamily A E I C) {n : ℕ} (s : I _⦋n⦌) :
    (nerveMap (F.cellFunctor s) ▷ (Δ[n] : SSet.{u + 1})) ≫
        strictSimplexCategoryEvaluation A E n =
      (nerve C ◁ (SSet.yonedaEquiv.symm (ULift.up s) :
        (Δ[n] : SSet.{u + 1}) ⟶ (SSet.uliftFunctor.{u + 1, u}).obj I)) ≫ F.evaluation := by
  apply SSet.hom_ext
  rintro ⟨⟨q⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨d, ⟨τ⟩⟩
  change ((strictSimplexCellFamily A E n).orderedSimplexFamily
      (d ⋙ F.cellFunctor s) (ULift.up τ)).diagonal =
    (F.orderedSimplexFamily d (I.map τ.op s)).diagonal
  apply congrArg OrderedSimplexFamily.diagonal
  apply OrderedSimplexFamily.ext
  · intro a
    exact (coherentDiagramSimplex_map (F.obj (d.obj a)) τ.toOrderHom s).symm
  · intro a b hab
    exact (F.map_pullback (d.map (homOfLE hab)) τ.toOrderHom s).symm

end StrictCoherentFamily
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
