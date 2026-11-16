module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeEquation

/-!
概要：元の全単体列に同じ probe を前置した、全次数の実 cone 単体を構成する。
方針：同じ実生データと全 HA 方程式をまとめ、単射制限と元の通常末尾面を回収する。
規約：同じ元の対象・射・符号付き選択 cochain を保持する。
使われ方：全作用素への自然性と大域 cone/prism の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HA.Section7_1_1
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorConeSimplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (n + 1) where
  toSimplexData := strictRawModuleTensorConeData A X P Q c
  equation := strictRawModuleTensorConeData_equation A X P Q c

lemma strictRawModuleTensorConeSimplex_data {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorConeSimplex A X P Q c).toSimplexData = strictRawModuleTensorConeData A X P Q c := rfl

lemma strictRawModuleTensorConeSimplex_pullback_injective {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) :
    (strictRawModuleTensorConeSimplex A X P Q c).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom) =
      strictRawModuleTensorConeSimplex A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data]
  exact strictRawModuleTensorConeData_pullback_injective A X P Q c e

lemma strictRawModuleTensorConeSimplex_tail {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorConeSimplex A X P Q c).pullback (Fin.succOrderEmb (n + 1)).toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ strictRawModuleTensorElementDiagram A X P Q) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data]
  exact strictRawModuleTensorConeData_tail A X P Q c

end SerrePositivity.EInfinity.BarrattEccles
