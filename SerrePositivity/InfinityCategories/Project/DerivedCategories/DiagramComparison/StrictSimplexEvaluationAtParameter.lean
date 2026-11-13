module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSimplexFunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FunctorCompositionEvaluation

/-!
概要：全 HA セルの評価を固定パラメーターへ制限し、元の同じ単体へ戻す。
方針：定値のパラメーター射列に対する全 HA 成分の比較を使う。
規約：頂点だけでなく全単体と全部分集合の成分を比較する。
使われ方：3b-3 R6、全余錐族と元の指定 native 余錐との比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (E : Type (u + 1)) [DGCategory A E]
  {C : Type (u + 1)} [Category.{u} C]

/-- curry した全族の頂点での評価は、元の全族の同じパラメーター制限。 -/
lemma strictFamilyCurry_evaluateAt {K : SSet.{u + 1}}
    (H : nerve C ⊗ K ⟶ dgNerve A E) (c : C) :
    MonoidalClosed.curry H ≫
        SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
          (ComposableArrows.mk₀ c) =
      lift (SSet.const (ComposableArrows.mk₀ c)) (𝟙 K) ≫ H := by
  let v : 𝟙_ SSet.{u + 1} ⟶ nerve C :=
    (SSet.unitHomEquiv (nerve C)).symm (ComposableArrows.mk₀ c)
  have h := SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.curry_evaluateFunctorAt_unitHomEquiv H v
  have hv : SSet.unitHomEquiv (nerve C) v = ComposableArrows.mk₀ c :=
    (SSet.unitHomEquiv (nerve C)).apply_symm_apply _
  rw [hv] at h
  have hg : (λ_ K).inv ≫ (v ▷ K) =
      lift (SSet.const (ComposableArrows.mk₀ c)) (𝟙 K) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  rw [← Category.assoc, hg] at h
  exact h

/-- 固定パラメーターでのセル評価は、元の同じ HA 単体の Yoneda 写像である。 -/
lemma strictSimplexFunctorEvaluation_atParameter {n : ℕ}
    (F : C ⥤ StrictSimplexCategory A E n) (c : C) :
    lift (SSet.const (ComposableArrows.mk₀ c)) (𝟙 (Δ[n] : SSet.{u + 1})) ≫
        strictSimplexFunctorEvaluation A E F =
      SSet.yonedaEquiv.symm (F.obj c).val := by
  apply SSet.hom_ext
  rintro ⟨⟨q⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨τ⟩
  change ((strictSimplexCellFamily A E n).orderedSimplexFamily
      ((((Functor.const (Fin (q + 1))).obj c) ⋙ F)) (ULift.up τ)).diagonal = _
  have hc : ((Functor.const (Fin (q + 1))).obj c) ⋙ F =
      (Functor.const (Fin (q + 1))).obj (F.obj c) := by
    apply CategoryTheory.Functor.hext
    · intro i
      rfl
    · intro i j f
      exact heq_of_eq (F.map_id c)
  rw [hc, StrictCoherentFamily.orderedSimplexFamily_const]
  rfl

/-- 元の native セルの全族を一つの図式へ制限すると、同じ native 単体に戻る。 -/
lemma strictBarNativeCellEvaluation_atParameter (J : Type) [SmallCategory J]
    (F : J ⥤ ModuleCategory A PUnit.{1}) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    lift (SSet.const (ComposableArrows.mk₀ F)) (𝟙 (Δ[n + 1] : SSet.{u + 1})) ≫
        strictBarNativeCellEvaluation A J s =
      SSet.yonedaEquiv.symm (strictBarNativeSimplex A J F s) :=
  strictSimplexFunctorEvaluation_atParameter A (RightModule A PUnit.{1})
    (strictBarNativeSimplexFunctor A J s) F

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
