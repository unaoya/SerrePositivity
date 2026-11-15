module
public import SerrePositivity.EInfinity.ComplexLimits.ConePrependIndex
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeComponents

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConePrependObjects

/-!
概要：始点付き単射による cone の対象と、通常部分の尾の添字を元の制限列へ戻す。
方針：零と後続元で元の定義を直接評価する。
規約：同じ元の対象を保持する。使われ方：全単射 pullback 成分の端点照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.ComplexLimits
open ConeHeadIndex
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_obj_prepend {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) (i : Fin (m + 2)) :
    (strictRawModuleTensorConeData A X P Q c).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom i) =
      (strictRawModuleTensorConeData A X P Q
        ((SimplexCategory.toCat.map
          (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)).obj i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl

end SerrePositivity.EInfinity.BarrattEccles
