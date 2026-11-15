module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeComponents
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-!
概要：実 cone の通常零次成分を元の frame 射の閉零元へ戻す。
方針：同じ通常成分の式と元の閉 nerve の零次成分式を合成する。
規約：元の frame 射・次数・cochain を保持する。
使われ方：同じ通常成分の単射再添字と元の合成項の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_hom_ordinary_closed {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) (hab : a ≤ b) :
    HEq ((strictRawModuleTensorConeData A X P Q c).hom I a b 0 hI ha hb hk)
      (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ ((strictRawModuleTensorElementDiagram A X P Q).map
          (c.map (homOfLE ((coneTailOrderHom n).monotone hab))))).val := by
  exact (strictRawModuleTensorConeData_hom_ordinary A X P Q c I a b 0 hI ha hb hk ha0).trans
    (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_zero _))

end SerrePositivity.EInfinity.BarrattEccles
