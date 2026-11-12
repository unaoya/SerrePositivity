module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.TrivialFibrationHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeInternalHomTrivialFibration

/-! 同じ基底と指定部分を持つ持ち上げを、両条件を全時間で固定して比較する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

lemma dgGluingRelativeHomotopy_of_trivialFibration_exists {D A E B : SSet.{u}}
    (i : D ⟶ A) [Mono i] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    (f g : A ⟶ E) (hi : i ≫ f = i ≫ g) (hp : f ≫ p = g ≫ p) :
    ∃ H : SSet.Homotopy f g,
      (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst D (Δ[1] : SSet.{u}) ≫ i ≫ g ∧
      H.h ≫ p = fst A (Δ[1] : SSet.{u}) ≫ g ≫ p := by
  let sq := Functor.PullbackObjObj.ofHasPullback internalHom i p
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration sq.π := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.trivialKanFibration_pullbackObjObjπ i p sq
  have hq : sq.π.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) =
      sq.π.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g) := by
    apply (SSet.yonedaEquiv (X := sq.pt) (n := ⦋0⦌)).symm.injective
    apply sq.hom_ext
    · rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp]
      apply congrArg SSet.yonedaEquiv.symm
      change (sq.π ≫ sq.fst).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) =
        (sq.π ≫ sq.fst).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)
      rw [sq.π_fst]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ f) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ g)
      rw [hi]
    · rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp]
      apply congrArg SSet.yonedaEquiv.symm
      change (sq.π ≫ sq.snd).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) =
        (sq.π ≫ sq.snd).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)
      rw [sq.π_snd]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ p) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ p)
      rw [hp]
  obtain ⟨k, hk⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_edge_over_trivialKanFibration sq.π
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g) hq
  have hfst : sq.π ≫ sq.fst = (pre i).app E := sq.π_fst
  have hsnd : sq.π ≫ sq.snd = (ihom A).map p := sq.π_snd
  have hvfst : sq.fst.app (Opposite.op ⦋0⦌)
      (sq.π.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ g) :=
    congrArg (fun q => q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)) hfst
  have hvsnd : sq.snd.app (Opposite.op ⦋0⦌)
      (sq.π.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ p) :=
    congrArg (fun q => q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)) hsnd
  let t : (Δ[1] : SSet.{u}) ⟶ (ihom A).obj E := SSet.yonedaEquiv.symm k.edge
  have he : t ≫ sq.π =
      (SSet.const (sq.π.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)) : Δ[1] ⟶ sq.pt) := by
    refine (SSet.yonedaEquiv_symm_comp k.edge sq.π).trans ?_
    refine (congrArg (SSet.yonedaEquiv (X := sq.pt) (n := ⦋1⦌)).symm hk).trans ?_
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _).symm
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge k, ?_, ?_⟩
  · change (i ▷ (Δ[1] : SSet.{u})) ≫ uncurry t = _
    rw [← uncurry_pre_app, ← hfst, ← Category.assoc, he, SSet.const_comp]
    exact (congrArg (fun v : ((ihom D).obj E) _⦋0⦌ =>
      uncurry (SSet.const v : (Δ[1] : SSet.{u}) ⟶ (ihom D).obj E)) hvfst).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex (i ≫ g))
  · change uncurry t ≫ p = _
    rw [← uncurry_natural_right, ← hsnd, ← Category.assoc, he, SSet.const_comp]
    exact (congrArg (fun v : ((ihom A).obj B) _⦋0⦌ =>
      uncurry (SSet.const v : (Δ[1] : SSet.{u}) ⟶ (ihom A).obj B)) hvsnd).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex (g ≫ p))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
