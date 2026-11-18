module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementSelected
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-!
概要：一点を選ぶ最上位普遍 cochain は元の Hom 複体の閉零元である。
方針：元の線形単体の微分方程式を使い、同じ最大点への移送を微分と両立させる。
規約：同じ選択 cochain を保つ。使われ方：実 cone の混合辺の HA 方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits

variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochain_closed {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    differential A (strictRawModuleTensorElementSelectedCochain A X P Q c J 0 hJ (by omega)) = 0 := by
  let s := strictRawModuleTensorElementLinear A X P Q
    ((SimplexCategory.toCat.map (strictRawModuleTensorElementSelection J hJ)).toFunctor ⋙ c)
  have hd : 0 = 1 - ((Finset.univ : Finset (Fin (J.card - 1 + 1))).card : ℤ) := by
    simp [hc]
  have hz : s.val.rhs Finset.univ 0 hd = 0 := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs
    exact dite_eq_right (by simp [hc])
  exact (s.equation Finset.univ 0 Finset.univ_nonempty hd).trans hz

lemma strictRawModuleTensorElementSelectedCochainAtMax_closed {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    differential A (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J 0 hJ (by omega)) =
      0 := by
  have hy : ForgetEnrichment.to (Complex A)
      ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (J.max' hJ))) =
      (ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj
        (c.obj ((strictRawModuleTensorElementSelection J hJ).toOrderHom (Fin.last (J.card - 1)))))) :=
    (congrArg (fun i => ForgetEnrichment.to (Complex A)
      ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj i)))
      (strictRawModuleTensorElementSelection_last J hJ)).symm
  have he : HEq (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J 0 hJ (by omega))
      (strictRawModuleTensorElementSelectedCochain A X P Q c J 0 hJ (by omega)) := cast_heq _ _
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := A) rfl hy rfl _ _ he
  exact eq_of_heq (hd.trans ((heq_of_eq
    (strictRawModuleTensorElementSelectedCochain_closed A X P Q c J hJ hc)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A) rfl hy rfl).symm))

end SerrePositivity.EInfinity.BarrattEccles
