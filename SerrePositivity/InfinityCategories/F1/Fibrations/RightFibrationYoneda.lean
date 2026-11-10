module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorRestrictionFiber
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorInitialEvaluation
public import SerrePositivity.InfinityCategories.F1B.Fibrations.RightAnodyneTensor
public import SerrePositivity.InfinityCategories.F1B.Cofinality.TerminalPointAnodyne
public import SerrePositivity.InfinityCategories.F1B.Cones.SliceIdentityTerminal
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulPostcomposition
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：right fibration への表現可能な相対射の全空間は、恒等点の fiber と同値。
方針：終対象の一点包含の right anodyne 性を相対関手の制限へ移す。
規約：実際の恒等点評価は自明 Kan fibration。分類同値や Yoneda 埋め込みを仮定しない。
使われ方：F1-2 の Yoneda 補題の right fibration 模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- right fibration を標的とする、底上の実際の全相対関手空間は Kan 複体。 -/
@[kerodon 01GZ]
instance relativeFunctorSpace_kanComplex_of_rightFibration {A E B : SSet.{u}}
    (p : E ⟶ B) [RightFibration p] (a : A ⟶ B) :
    KanComplex (relativeFunctorSpace p a) :=
  vertexFiber_kanComplex ((ihom A).map p) (functorVertex a)

/-- right anodyne な始域の制限は、全相対関手空間上で自明 Kan fibration。 -/
lemma relativeFunctorPre_trivialKanFibration_of_rightAnodyne {A D E B : SSet.{u}}
    (p : E ⟶ B) [RightFibration p] (a : A ⟶ B) (i : D ⟶ A)
    (hi : rightAnodyneExtensions i) : TrivialKanFibration (relativeFunctorPre p a i) := by
  let sq' := CategoryTheory.Functor.PullbackObjObj.ofHasPullback internalHom i p
  have := cofinalTrivialKanFibration_relativeHom_of_rightAnodyne i hi p sq'
  exact relativeFunctorPre_trivialKanFibration_of_relativeHom p a i sq'

/-- right anodyne な点包含への相対評価は、全境界を固定して持ち上げられる。 -/
lemma relativeFunctorEvaluate_trivialKanFibration_of_rightPointMap {A E B : SSet.{u}}
    (p : E ⟶ B) [RightFibration p] (a : A ⟶ B)
    (i : (Δ[0] : SSet.{u}) ⟶ A) (hi : rightAnodyneExtensions i) :
    TrivialKanFibration (relativeFunctorEvaluate p a
      (i.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))) := by
  rw [← relativeFunctorPre_point_evaluate p a i]
  exact ⟨trivialKanFibrations.comp_mem _ _
    (relativeFunctorPre_trivialKanFibration_of_rightAnodyne p a i hi).mem
    (MorphismProperty.rlp_of_isIso _ _)⟩

/-- 始域の終対象での実際の相対関手評価は自明 Kan fibration。 -/
lemma relativeFunctorEvaluate_terminal_trivialKanFibration {A E B : SSet.{u}}
    (p : E ⟶ B) [RightFibration p] (a : A ⟶ B) (v : A _⦋0⦌)
    (hv : IsTerminalVertex v) : TrivialKanFibration (relativeFunctorEvaluate p a v) := by
  have h := relativeFunctorEvaluate_trivialKanFibration_of_rightPointMap p a
    (SSet.yonedaEquiv.symm v) (SerrePositivity.InfinityCategories.F1B.terminalPoint_rightAnodyne hv)
  have hp : (stdSimplex.obj₀Equiv.symm 0 : (Δ[0] : SSet.{u}) _⦋0⦌) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    omega
  rw [hp, SSet.yonedaEquiv_symm_app_id] at h
  exact h

/-- 表現可能な right fibration からの相対射を恒等点で評価し、元の fiber へ正規化する。 -/
def rightFibrationSlicePointEvaluate {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    relativeFunctorSpace p (sliceOverProjection (SSet.yonedaEquiv.symm b)) ⟶ vertexFiber p b :=
  relativeFunctorEvaluate p (sliceOverProjection (SSet.yonedaEquiv.symm b))
    (sliceIdentityCone b) ≫
      eqToHom (congrArg (vertexFiber p) (sliceIdentityCone_projection b))

/-- Yoneda の実際の恒等点評価は、全高次パラメーターで自明 Kan fibration。 -/
lemma rightFibrationSlicePointEvaluate_trivialKanFibration
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [RightFibration p] (b : B _⦋0⦌) :
    TrivialKanFibration (rightFibrationSlicePointEvaluate p b) := by
  have h := relativeFunctorEvaluate_terminal_trivialKanFibration p
    (sliceOverProjection (SSet.yonedaEquiv.symm b)) (sliceIdentityCone b)
    (SerrePositivity.InfinityCategories.F1B.sliceIdentityCone_isTerminalVertex b)
  exact ⟨trivialKanFibrations.comp_mem _ _ h.mem (MorphismProperty.rlp_of_isIso _ _)⟩

/-- Yoneda 補題：表現可能な right fibration からの全相対射は、指定 fiber と同値。 -/
lemma rightFibrationSlicePointEvaluate_isQCatEquivalence
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [RightFibration p] (b : B _⦋0⦌) :
    IsQCatEquivalence (rightFibrationSlicePointEvaluate p b) := by
  have := vertexFiber_kanComplex p b
  have := rightFibrationSlicePointEvaluate_trivialKanFibration p b
  exact isQCatEquivalence_of_trivialKanFibration _

/-- 同じ Yoneda 評価を順方向とする、全写像空間の実際の同値データ。 -/
def rightFibrationYonedaEquivalence
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [RightFibration p] (b : B _⦋0⦌) :
    QCatEquivalence
      (relativeFunctorSpace p (sliceOverProjection (SSet.yonedaEquiv.symm b)))
      (vertexFiber p b) := by
  have := vertexFiber_kanComplex p b
  exact (rightFibrationSlicePointEvaluate_isQCatEquivalence p b).choose

end SerrePositivity.InfinityCategories
