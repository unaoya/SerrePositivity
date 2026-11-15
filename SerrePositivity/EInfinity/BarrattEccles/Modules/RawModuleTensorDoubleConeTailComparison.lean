module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementAugmentedColumnTerminal
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeTailTerminal

/-!
概要：実二重 cone の末尾単体は、元の通常 augmentation の終端付き列の閉単体に等しい。
方針：全前面を同じ frame 単体へ戻し、全終端成分を同じ augmentation へ照合する。
規約：HA Construction 1.3.1.13、対象と全高次 cochain の厳密な一致。使われ方：大域 slice 評価と元の円柱の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.EInfinity.Modules SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeTail_eq_closed {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    strictRawModuleTensorDoubleConeTail A X P Q c =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (strictRawModuleTensorElementAugmentedColumn A X P Q c) := by
  have hf := (strictRawModuleTensorDoubleConeTail_front A X P Q c).trans
    (strictRawModuleTensorElementAugmentedColumn_closed_front A X P Q c).symm
  have ho : (strictRawModuleTensorDoubleConeTail A X P Q c).obj =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
        (strictRawModuleTensorElementAugmentedColumn A X P Q c)).obj := by
    funext i
    induction i using Fin.lastCases with
    | last =>
      change (strictRawModuleTensorDoubleConeSimplex A X P Q c).obj
        (doubleConeTailOrderHom n (Fin.last (n + 1))) =
        (ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementAugmentedColumn A X P Q c).obj (Fin.last (n + 1))))
      rw [doubleConeTailOrderHom_last, strictRawModuleTensorDoubleConeSimplex_last,
        strictRawModuleTensorElementAugmentedColumn_obj_last]
    | cast i => exact congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) n => s.obj i) hf
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext ho
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise ho
  intro I a b k hI ha hb hk
  by_cases hbl : b = Fin.last (n + 1)
  · exact (strictRawModuleTensorDoubleConeTail_hom_last A X P Q c I a b k hI ha hb hk hbl).trans
      (strictRawModuleTensorElementAugmentedColumn_hom_last A X P Q c I a b k hI ha hb hk hbl).symm
  · have hf' := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData hf
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data] at hf'
    exact moduleSimplexData_hom_heq_of_front_eq A (dgAlgebraCategory A ((assocForget A).obj X)) _ _ hf' I a b k hI ha hb hk hbl

end SerrePositivity.EInfinity.BarrattEccles
