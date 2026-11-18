module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementAugmentedColumnMaps
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeMap
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DoubleConeTailIndex

/-!
概要：通常終端付き列と二重 cone の末尾単体は、どちらも同じ元の全 frame 前面を持つ。
方針：実列の通常射を元の図式へ戻し、二重 cone の二つの前面制限を交換する。
規約：HA Construction 1.3.1.13、全高次成分を同じ通常閉単体へ回収する。使われ方：終端以外の全 cochain の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.EInfinity.Modules _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementAugmentedColumn_front {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    Fin.castSuccOrderEmb.toOrderHom.monotone.functor ⋙
      strictRawModuleTensorElementAugmentedColumn A X P Q c =
      c ⋙ strictRawModuleTensorElementDiagram A X P Q := by
  apply CategoryTheory.Functor.hext (strictRawModuleTensorElementAugmentedColumn_obj_castSucc A X P Q c)
  intro i j f
  exact strictRawModuleTensorElementAugmentedColumn_map_cast_cast A X P Q c i j (leOfHom f)

lemma strictRawModuleTensorElementAugmentedColumn_closed_front {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
      (strictRawModuleTensorElementAugmentedColumn A X P Q c)).pullback
      Fin.castSuccOrderEmb.toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ strictRawModuleTensorElementDiagram A X P Q) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveSimplex_pullback]
  exact congrArg (fun F => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (F))
    (strictRawModuleTensorElementAugmentedColumn_front A X P Q c)

def strictRawModuleTensorDoubleConeTail {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (n + 1) :=
  (strictRawModuleTensorDoubleConeSimplex A X P Q c).pullback (_root_.SerrePositivity.ComplexLimits.doubleConeTailOrderHom n)

lemma strictRawModuleTensorDoubleConeTail_front {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorDoubleConeTail A X P Q c).pullback Fin.castSuccOrderEmb.toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ strictRawModuleTensorElementDiagram A X P Q) := by
  have hindex : (_root_.SerrePositivity.ComplexLimits.doubleConeTailOrderHom n).comp Fin.castSuccOrderEmb.toOrderHom =
      Fin.castSuccOrderEmb.toOrderHom.comp (Fin.succOrderEmb (n + 1)).toOrderHom := by
    apply DFunLike.ext
    intro i
    exact _root_.SerrePositivity.ComplexLimits.doubleConeTailOrderHom_castSucc n i
  rw [strictRawModuleTensorDoubleConeTail, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp, hindex, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp,
    strictRawModuleTensorDoubleConeSimplex_front, strictRawModuleTensorConeSimplex_tail]

end SerrePositivity.EInfinity.BarrattEccles
