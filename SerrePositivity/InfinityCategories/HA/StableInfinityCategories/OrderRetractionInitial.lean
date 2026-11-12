module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.InitialJoinIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCorePunctured
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetInteriorPrism
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PullbackConeVertex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ThinNerveConeComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ThinNerveMonomorphism

/-!
概要：比較格子の初期角を実引き戻しへ置換し、矢印圏の普遍性へ接続する。
方針：穿孔格子の同じ錐と全非初期単体を厳密に保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma orderRetraction_leftAnodyne {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (i : P →o Q) (r : Q →o P) (hri : Function.LeftInverse r i)
    (hir : ∀ q, i (r q) ≤ q) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (nerveMap i.toFunctor) := by
  have : Mono (nerveMap i.toFunctor) :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.nerveMap_mono_of_thin_of_obj_injective i.toFunctor hri.injective
  have hs : nerveMap i.toFunctor ≫ nerveMap r.toFunctor = 𝟙 (nerve P) := by
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
    intro v
    exact hri (nerveEquiv v)
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftAnodyneExtensions_of_fixed_initial_homotopy _ (nerveMap r.toFunctor) hs
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetInteriorPrism (i.comp r) hir)
  · rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetInteriorPrism_zero]
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
    intro v
    rfl
  · exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetInteriorPrism_one _ _
  · apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
    intro v
    change (if (stdSimplex.objEquiv v.1).toOrderHom 0 = 0
      then i (r (i (nerveEquiv v.2))) else i (nerveEquiv v.2)) = i (nerveEquiv v.2)
    split
    · exact congrArg i (hri _)
    · rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
