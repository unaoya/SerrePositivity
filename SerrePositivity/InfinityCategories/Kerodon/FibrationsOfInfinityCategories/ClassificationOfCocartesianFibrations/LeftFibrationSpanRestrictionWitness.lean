module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationSpanStrictification

/-!
概要：既存のspanの厳密化の証明で得られる、同じ指定制限との比較を残す。
方針：既存の相対関手空間の前合成同値から、元の証明中の同じ同型を回収する。
規約：Kerodon Corollary 5.6.0.6（Tag 028T）、HTT §3.3.2の既存構成の制限の法則。
使われ方：S8の復元比較で、指定spanと両立することを選択条件に保つための証明部品。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の厳密化の証明中の制限同型を、同じspanの比較の証拠として保持する。 -/
lemma exists_leftFibration_comparison_of_span_with_restriction
    {E F Z B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration q] (r : Z ⟶ B)
    (a : Z ⟶ E) (b : Z ⟶ F) (ha : a ≫ p = r) (hb : b ≫ q = r)
    (ea : IsPrecompositionEquivalence a) (eb : IsPrecompositionEquivalence b) :
    ∃ (f : E ⟶ F) (hf : f ≫ q = p), IsPrecompositionEquivalence f ∧
      Nonempty (VertexIso
        ((relativeFunctorOverPre q (show Over.mk r ⟶ Over.mk p from Over.homMk a ha)).app (Opposite.op ⦋0⦌)
          (relativeFunctorVertex q p f hf))
        (relativeFunctorVertex q r b hb)) := by
  have : Quasicategory F := quasicategory_of_innerFibration q
  let a' : Over.mk r ⟶ Over.mk p := Over.homMk a ha
  have he := relativeFunctorOverPre_isQCatEquivalence q a' ea
  obtain ⟨v, ⟨h⟩⟩ := he.choose.isEssentiallySurjective (relativeFunctorVertex q r b hb)
  obtain ⟨f, hf, hv⟩ := exists_relativeFunctorVertex q p v
  rw [← hv] at h
  have h' : FunctorIso (a ≫ f) b :=
    h.map (vertexFiberι ((ihom Z).map q) (functorVertex r))
  have hcomp : IsPrecompositionEquivalence (a ≫ f) :=
    (isPrecompositionEquivalence_iff_of_homotopy h'.simplicialHomotopy
      (simplicialHomotopyOfFunctorEdge_vertex_isInvertible
        (FunctorIso.edge h') (FunctorIso.edge_isInvertible h'))).mpr eb
  exact ⟨f, hf, ea.cancel_left hcomp, ⟨h⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
