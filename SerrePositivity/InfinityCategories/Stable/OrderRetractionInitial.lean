module
public import SerrePositivity.InfinityCategories.Stable.PosetInteriorPrism
public import SerrePositivity.InfinityCategories.Stable.ExcisionCorePunctured
public import SerrePositivity.InfinityCategories.Stable.ThinNerveMonomorphism
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialJoinIso
public import SerrePositivity.InfinityCategories.Stable.ThinNerveConeComparison
public import SerrePositivity.InfinityCategories.Stable.PullbackConeVertex
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConeValEquality
public import SerrePositivity.InfinityCategories.Stable.ExcisionSquareGrid
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanBoundary

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
namespace SerrePositivity.InfinityCategories

lemma orderRetraction_leftAnodyne {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (i : P →o Q) (r : Q →o P) (hri : Function.LeftInverse r i)
    (hir : ∀ q, i (r q) ≤ q) : leftAnodyneExtensions (nerveMap i.toFunctor) := by
  have : Mono (nerveMap i.toFunctor) :=
    nerveMap_mono_of_thin_of_obj_injective i.toFunctor hri.injective
  have hs : nerveMap i.toFunctor ≫ nerveMap r.toFunctor = 𝟙 (nerve P) := by
    apply thinNerveHom_ext_of_vertices
    intro v
    exact hri (nerveEquiv v)
  apply leftAnodyneExtensions_of_fixed_initial_homotopy _ (nerveMap r.toFunctor) hs
    (posetInteriorPrism (i.comp r) hir)
  · rw [posetInteriorPrism_zero]
    apply thinNerveHom_ext_of_vertices
    intro v
    rfl
  · exact posetInteriorPrism_one _ _
  · apply thinNerveHom_ext_of_vertices
    intro v
    change (if (stdSimplex.objEquiv v.1).toOrderHom 0 = 0
      then i (r (i (nerveEquiv v.2))) else i (nerveEquiv v.2)) = i (nerveEquiv v.2)
    split
    · exact congrArg i (hri _)
    · rfl

end SerrePositivity.InfinityCategories
