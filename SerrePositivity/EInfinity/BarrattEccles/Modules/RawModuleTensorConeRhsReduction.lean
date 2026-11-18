module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeQuadratic
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConePenultimateCuts

/-!
概要：実 cone の全 HA 右辺を削除和と一つの元の終端切断合成へ還元する。
方針：全非線形和の支持と元の最後の切断の符号を使う。
規約：元の実データ・全有限和・同じ切断成分を保持する。
使われ方：残る混合 HA 方程式の線形右辺との照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_rhs_reduced {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) :
    (strictRawModuleTensorConeData A X P Q c).rhs I a b k hI ha hb hk =
    (strictRawModuleTensorConeData A X P Q c).linearBoundary I a b k +
      (strictRawModuleTensorConeData A X P Q c).cutCompose I a b k (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_eq_linear_sub_quadratic,
    strictRawModuleTensorConeData_quadratic_single A X P Q c I a b k hI ha hb hk hc,
    _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.sign_penultimate]
  simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_one_smul, sub_neg_eq_add]

end SerrePositivity.EInfinity.BarrattEccles
