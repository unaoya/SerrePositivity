module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeTail
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EquationTransfer

/-!
概要：実 cone の始頂点を含まない全ての成分が HA 方程式を満たす。
方針：元の frame 単体への実制限の一致から、同じ像の集合へ方程式を戻す。
規約：任意次数・全有限部分集合を保持する。使われ方：残る混合成分の方程式への還元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.ComplexLimits ConeHeadIndex
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_equation_without_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (h0 : (0 : Fin (n + 2)) ∉ I) :
    (strictRawModuleTensorConeData A X P Q c).Equation I := by
  have h := (strictRawModuleTensorConeData A X P Q c).equation_image_of_pullback
    (Fin.succOrderEmb (n + 1)).toOrderHom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ strictRawModuleTensorElementDiagram A X P Q))
    (strictRawModuleTensorConeData_tail A X P Q c) (withoutFirst I) (Fin.succ_injective _).injOn
  have hi : (withoutFirst I).image (Fin.succOrderEmb (n + 1)).toOrderHom = I := by
    change (withoutFirst I).image Fin.succ = I
    rw [image_withoutFirst, Finset.erase_eq_of_notMem h0]
  simpa only [hi] using h

end SerrePositivity.EInfinity.BarrattEccles
