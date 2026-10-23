module
public import SerrePositivity.InfinityCategories.F1.Weighted.CosliceTransport
public import SerrePositivity.InfinityCategories.F1.Universe.Reflection
public import SerrePositivity.InfinityCategories.F1B.KanQCatEquivalenceOpposite
/-!
概要：同じ豊穣後合成が同値なら、coherent nerve の実 coslice 輸送も同値。
方針：指定閉射を二点の実通常図式に束ね、既存の weighted coslice prism と両 fiber 比較を使う。
規約：全ての射影・係数・実辺は同じもの。使われ方：dg の実後合成と coslice 輸送の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
/-- 豊穣 Hom の同じ実後合成が同値なら、その coherent な実辺の coslice 輸送は同値。 -/
lemma dgCoherentCosliceTransport_isQCatEquivalence_of_sHom
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [Quasicategory (SimplicialNerve C)] [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    (x : C) {y z : C} (f : y ⟶ z)
    (hf : IsQCatEquivalence (eHomWhiskerLeft SSet x f)) :
    IsQCatEquivalence (edgeTransport
      (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
      (coherentNerveEdge f)) := by
  let F : ULift.{u} (Fin 2) ⥤ C :=
    (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin 2) →o Fin 2).toFunctor ⋙
      ComposableArrows.mk₁ f
  let g := homOfLE (show (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ≤ ULift.up 1 from by decide)
  let (i : ULift.{u} (Fin 2)) :
      KanComplex ((HomotopyLimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).obj i) :=
    inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)).op)
  have hc : IsQCatEquivalence
      ((HomotopyLimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).map g) := by
    change IsQCatEquivalence (SSet.opFunctor.map (eHomWhiskerLeft SSet x f))
    exact F1B.kanIsQCatEquivalence_op hf
  have hu := (isQCatEquivalence_ulift_iff_of_kan.{u, v}
    ((HomotopyLimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).map g)).mpr hc
  have hy := (HomotopyLimits.coherentCosliceFiberComparison_homotopyEquivalence
    x y).isQCatEquivalence
  have hz := (HomotopyLimits.coherentCosliceFiberComparison_homotopyEquivalence
    x z).isQCatEquivalence
  exact hy.cancel_left ((hu.comp hz).ofFunctorIso
    (coherentCosliceFiberComparison_transportIso F x g))
end SerrePositivity.InfinityCategories
