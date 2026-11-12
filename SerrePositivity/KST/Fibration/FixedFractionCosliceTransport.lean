module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.FractionFamilyCoslice

/-! # 固定分数の終点表示の輸送は、元の同じ coslice fiber 評価と可換 -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q) (W : Set (X _⦋1⦌))
  (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W) (x : X _⦋0⦌)

/-- 終点の等式による輸送は、同じ分数評価の実 fiber 写像と厳密に可換。 -/
theorem fixedFractionCosliceEvaluation_transport {y z : X _⦋0⦌} (e : y = z) :
    eqToHom (congrArg (fun a => fixedMarkedSpans X W x a) e) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionCosliceEvaluation F W hF x z =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionCosliceEvaluation F W hF x y ≫ eqToHom
        (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x))))
          (congrArg (F.app (Opposite.op ⦋0⦌)) e)) := by
  cases e
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 逆向きに表示を揃えた同じ入力点を評価し、順向きに戻せば、元の評価点を厳密に回収する。 -/
theorem fixedFractionCosliceEvaluation_transport_vertex {y z : X _⦋0⦌} (e : y = z)
    (s : (fixedMarkedSpans X W x z) _⦋0⦌) :
    (eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x))))
      (congrArg (F.app (Opposite.op ⦋0⦌)) e))).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionCosliceEvaluation F W hF x y).app (Opposite.op ⦋0⦌)
          ((eqToHom (congrArg (fun a => fixedMarkedSpans X W x a) e.symm)).app
            (Opposite.op ⦋0⦌) s)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionCosliceEvaluation F W hF x z).app (Opposite.op ⦋0⦌) s := by
  cases e
  rfl

end SerrePositivity.KST.Fibration
