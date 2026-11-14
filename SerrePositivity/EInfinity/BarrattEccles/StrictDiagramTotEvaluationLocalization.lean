module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotLocalization
public import SerrePositivity.EInfinity.BarrattEccles.CAlgQuasiIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathInternalHom
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences

/-!
概要：元のstrict BE全評価を、同じobjectwise擬同型の局所化へ降ろす。
方針：各点の既存algebraCAlgSourceによる反転と局所化の全関手普遍性。
規約：IS-W2 R05の因子化。評価比較の同値やBE図式の厳密化は結論しない。
使われ方：指定全錐の右境界と、局所化上のU比較の全評価。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A]

/-- 同じ全strict BE評価を全図式射のパラメータにcurryする。 -/
def strictBETotDiagramFamily : StrictBETotDiagramNerve A ⟶
    (ihom ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))).obj
      (CAlg_R A) := curry (strictBECosimplicialEvaluation A)

/-- 点での全評価は元の同じ通常評価のnerveに一致。 -/
theorem strictBETotDiagramFamily_evaluation (j : AsSmall.{u} SimplexCategory) :
    strictBETotDiagramFamily A ≫ evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ j)) =
      nerveMap ((CategoryTheory.evaluation (AsSmall.{u} SimplexCategory)
        (operad A).Algebra).obj j) ≫ algebraCAlgSource A := by
  rw [strictBETotDiagramFamily, curry_evaluateFunctorAt_vertex]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change (algebraCAlgSource A).app (Opposite.op ⦋n⦌) _ =
    (algebraCAlgSource A).app (Opposite.op ⦋n⦌) _
  congr 1
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro i
    rfl
  intro i k f
  change (s.obj i).map (𝟙 j) ≫ (s.map f).app j = (s.map f).app j
  simp

/-- 同じ全評価は指定したobjectwise擬同型を可逆にする。 -/
theorem strictBETotDiagramFamily_inverts :
    InvertsEdges (strictBETotDiagramFamily A) (strictBETotDiagramWeakEdges A) := by
  intro s hs
  obtain ⟨F, G, f, rfl⟩ := ComposableArrows.mk₁_surjective s
  apply (isInvertibleEdge_iff_evaluateFunctorAt_any _).mpr
  rintro ⟨v⟩
  obtain ⟨j, rfl⟩ := nerveEquiv.symm.surjective v
  have h := algebraCAlgSource_map_weak A (f.app j) (hs j)
  apply (isInvertibleEdge_congr (f := ((nerve.edgeMk (f.app j)).map (algebraCAlgSource A)).toTruncated) ?_).mpr h
  change (strictBETotDiagramFamily A ≫ evaluateFunctorAt
    (ULift.up (ComposableArrows.mk₀ j))).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f) = _
  rw [strictBETotDiagramFamily_evaluation]
  change (algebraCAlgSource A).app (Opposite.op ⦋1⦌)
    ((nerveMap ((CategoryTheory.evaluation (AsSmall.{u} SimplexCategory)
      (operad A).Algebra).obj j)).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f)) =
    (algebraCAlgSource A).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ (f.app j))
  rw [nerveMap_app_mk₁]
  rfl

/-- 元の全strict評価の、指定局所化からの全関手の延長の存在。 -/
theorem exists_strictBETotLocalizedEvaluation :
    ∃ ev : StrictBETotDiagramInfinity A ⟶
        (ihom ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))).obj
          (CAlg_R A),
      Nonempty (FunctorIso (strictBETotDiagramLocalization A ≫ ev)
        (strictBETotDiagramFamily A)) :=
  (strictBETotDiagramLocalization_isLocalization A).exists_extension
    (strictBETotDiagramFamily A) (strictBETotDiagramFamily_inverts A)

/-- 同じ全図式射を持つ局所化上の実評価。 -/
def strictBETotLocalizedEvaluation : StrictBETotDiagramInfinity A ⟶
    (ihom ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))).obj
      (CAlg_R A) := (exists_strictBETotLocalizedEvaluation A).choose

/-- 延長の指定全同型は元の全strict評価を保持する。 -/
def strictBETotLocalizedEvaluation_factor :
    FunctorIso (strictBETotDiagramLocalization A ≫ strictBETotLocalizedEvaluation A)
      (strictBETotDiagramFamily A) :=
  (exists_strictBETotLocalizedEvaluation A).choose_spec.some

end SerrePositivity.EInfinity.BarrattEccles
