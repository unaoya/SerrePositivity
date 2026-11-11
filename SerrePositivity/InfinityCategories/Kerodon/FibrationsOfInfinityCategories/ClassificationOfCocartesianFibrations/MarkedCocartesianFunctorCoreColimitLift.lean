module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.MarkedCocartesianFunctorColimitDescent
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.MarkedCocartesianFunctorCoreVertexDescent
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SectionCoreColimitLift

/-!
概要：指定辺を保つ元の Hom の core の族を、指定辺を覆う余極限へ貼る。
方針：全相対 Hom の族を貼り、頂点の被覆によって core への所属を回収する。
規約：指定辺の被覆と底上の全空間の余極限の両方を明示する。
使われ方：元の cocartesian Hom の全高次の降下。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {J : Type v} [Category.{w} J] {T E B : SSet.{u}} (q : E ⟶ B) (D : J ⥤ Over B)
  (W : ∀ j, Set ((D.obj j).left _⦋1⦌))
  (hW : ∀ {j k} (f : j ⟶ k) e, e ∈ W j → (D.map f).left.app (Opposite.op ⦋1⦌) e ∈ W k)
  (s : ∀ j, T ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace q (D.obj j).hom (W j)) : SSet.{u}))
  (hs : ∀ {j k} (f : j ⟶ k), s j = s k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q (D.map f) (W j) (W k) (hW f)))

include hs in
/-- core の族の元の全相対 Hom の族は、同じ制限に関して厳密に整合する。 -/
lemma markedCocartesianCoreFamily_underlying_compatible {j k : J} (f : j ⟶ k) :
    s j ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace q (D.obj j).hom (W j))).ι =
      (s k ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace q (D.obj k).hom (W k))).ι) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q (D.map f) (W j) (W k) (hW f) := by
  rw [hs f, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι, ← Category.assoc]

/-- 元の指定辺を保つ Hom の core の族を、同じ余極限上へ貼る。 -/
def markedCocartesianCoreFamilyColimitLift [Small.{u} J] [Quasicategory B] [InnerFibration q]
    (c : Cocone D) (hc : IsColimit ((Over.forget B).mapCocone c))
    (U : Set (c.pt.left _⦋1⦌))
    (hU : ∀ e ∈ U, ∃ j t, t ∈ W j ∧ (c.ι.app j).left.app (Opposite.op ⦋1⦌) t = e)
    (hi : ∀ j e, e ∈ W j → (c.ι.app j).left.app (Opposite.op ⦋1⦌) e ∈ U) :
    T ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace q c.pt.hom U) : SSet.{u}) := by
  let s' := fun j ↦ s j ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace q (D.obj j).hom (W j))).ι
  have hs' : ∀ {j k} (f : j ⟶ k), s' j =
      s' k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q (D.map f) (W j) (W k) (hW f) :=
    fun {j k} f ↦ markedCocartesianCoreFamily_underlying_compatible q D W hW s hs f
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFamilyColimitLift q D W hW s' hs' c hc U hU
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift g (by
    intro e
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isInvertibleEdge_markedCocartesianFunctor_of_vertex_cover q c.pt D.obj c.ι.app U W hi
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionColimit_vertex_cover c hc)
    intro j
    have hf := congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌) e)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFamilyColimitLift_fac q D W hW s' hs' c hc U hU hi j)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (g.app (Opposite.op ⦋1⦌) e)).map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q (c.ι.app j) (W j) U (hi j))))
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((s j).app (Opposite.op ⦋1⦌) e).val) hf).mpr
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_edge _))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
