module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.CosliceTwistedHomEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceIntervalNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful

/-!
概要：元の twisted Hom に関手の実際の写像を与え、元の coslice 比較の自然性を示す。
方針：元の全 twisted arrow の後合成を同じ両端の fiber に制限する。
規約：元の各全単体と元の関手の後合成を保持する。
使われ方：充満忠実な元の関手の共同 Hom 図式の全自然比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の関手の twisted arrow 写像を、元の両端の twisted Hom に厳密に制限する。 -/
def twistedHomFunctorMap {C D : SSet.{u}} (f : C ⟶ D) (x y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpace x y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpace (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection D)
    (SSet.opObjEquiv.symm (f.app (Opposite.op ⦋0⦌) x), f.app (Opposite.op ⦋0⦌) y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (SSet.opObjEquiv.symm x, y) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f) (by
        rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_naturality, ← Category.assoc,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp]
        rfl)

/-- 元の twisted Hom 写像は、全単体の同じ元の後合成そのもの。 -/
lemma twistedHomFunctorMap_app_val {C D : SSet.{u}} (f : C ⟶ D) (x y : C _⦋0⦌)
    {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpace x y) _⦋n⦌) :
    ((twistedHomFunctorMap f x y).app (Opposite.op ⦋n⦌) s).val = s.val ≫ f := rfl

/-- 元の coslice fiber の全単体を展開すると、同じ元の付随錐を回収する。 -/
lemma cosliceFiberUncurry_yoneda {C : SSet.{u}} {x y : C _⦋0⦌} {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry (SSet.yonedaEquiv.symm s) = s.val.val := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry
  rw [SSet.yonedaEquiv_symm_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda]
  rfl

/-- 元の coslice fiber 写像は、元の各全錐の後合成そのもの。 -/
lemma pointCosliceFiberMap_app_val {C D : SSet.{u}} (f : C ⟶ D) (x y : C _⦋0⦌)
    {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋n⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceFiberMap f x y).app (Opposite.op ⦋n⦌) s).val.val = s.val.val ≫ f := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceFiberMap_uncurry (SSet.yonedaEquiv.symm s) f
  rw [SSet.yonedaEquiv_symm_comp, cosliceFiberUncurry_yoneda,
    cosliceFiberUncurry_yoneda] at h
  exact h

/-- 元の twisted Hom 比較は、元の関手の両写像空間への作用と全単体で可換。 -/
lemma cosliceTwistedHomMap_functor {C D : SSet.{u}} (f : C ⟶ D) (x y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceTwistedHomMap x y ≫ twistedHomFunctorMap f x y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceFiberMap f x y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceTwistedHomMap (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change ((twistedHomFunctorMap f x y).app (Opposite.op ⦋n⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceTwistedHomMap x y).app (Opposite.op ⦋n⦌) s)).val =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceTwistedHomMap (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)).app
      (Opposite.op ⦋n⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceFiberMap f x y).app (Opposite.op ⦋n⦌) s)).val
  rw [twistedHomFunctorMap_app_val, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceTwistedHomMap_app_val,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceTwistedHomMap_app_val, pointCosliceFiberMap_app_val, Category.assoc]

/-- 元の充満忠実な関手の同じ twisted Hom 写像自身は、実際の同値。 -/
lemma twistedHomFunctorMap_isQCatEquivalence {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f)
    (x y : C _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (twistedHomFunctorMap f x y) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceFiberMap_equivalence_iff_pinchedHomMap f x y).mpr (hf x y)
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceTwistedHomMap_isQCatEquivalence x y
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceTwistedHomMap_isQCatEquivalence
    (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)
  apply hc.cancel_left
  rw [cosliceTwistedHomMap_functor]
  exact h.comp hd

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
