module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DoubleConeIndex
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeSimplex

/-!
概要：二重 cone の対象と全前面制限は、元の任意作用素による制限と整合する。
方針：対象は終点と前面に分け、前面全体は既存の cone の全自然性へ戻す。
規約：HA Construction 1.3.1.6・1.3.1.13、退化も含む全作用素。使われ方：全通常成分の自然性。
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
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeSimplex_obj_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (i : Fin (m + 3)) :
    (strictRawModuleTensorDoubleConeSimplex A X P Q c).obj (_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom θ i) =
      (strictRawModuleTensorDoubleConeSimplex A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).obj i := by
  induction i using Fin.lastCases with
  | last => rw [_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom_last, strictRawModuleTensorDoubleConeSimplex_last,
      strictRawModuleTensorDoubleConeSimplex_last]
  | cast i =>
    rw [_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom_castSucc]
    change moduleRightConeObj A (dgAlgebraCategory A ((assocForget A).obj X)) (strictRawModuleTensorConeSimplex A X P Q c) ((strictRawModuleProbeFunctor A X).obj P)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom i).castSucc =
      moduleRightConeObj A (dgAlgebraCategory A ((assocForget A).obj X)) (strictRawModuleTensorConeSimplex A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ((strictRawModuleProbeFunctor A X).obj P) i.castSucc
    rw [moduleRightConeObj_castSucc, moduleRightConeObj_castSucc]
    exact strictRawModuleTensorConeData_obj_prepend_map A X P Q c θ i

lemma strictRawModuleTensorDoubleConeSimplex_pullback_front {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    ((strictRawModuleTensorDoubleConeSimplex A X P Q c).pullback (_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom θ)).pullback
      Fin.castSuccOrderEmb.toOrderHom =
      (strictRawModuleTensorDoubleConeSimplex A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).pullback
        Fin.castSuccOrderEmb.toOrderHom := by
  have hindex : (_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom θ).comp Fin.castSuccOrderEmb.toOrderHom =
      Fin.castSuccOrderEmb.toOrderHom.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom) := by
    apply DFunLike.ext
    intro i
    exact _root_.SerrePositivity.ComplexLimits.doubleConeOrderHom_castSucc θ i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp, hindex, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp,
    strictRawModuleTensorDoubleConeSimplex_front, strictRawModuleTensorDoubleConeSimplex_front,
    strictRawModuleTensorConeSimplex_pullback_map]

end SerrePositivity.EInfinity.BarrattEccles
