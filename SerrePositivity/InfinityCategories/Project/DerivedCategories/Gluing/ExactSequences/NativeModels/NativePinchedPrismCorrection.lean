module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.FunctorPinchedSimplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.NativeModels.NativeAugmentationPrimitive
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CommaComparisons.CommaPinchedPrismLinearCorrection

/-! 元の augmentation prism の唯一の補正を、元 gluing Hom の実 primitive の Yoneda 像へ戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
  {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M} {n : ℕ}
  (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X Y) _⦋n⦌)

def dgGluingNativeCommaPinchedSimplex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R D (RightModule R C) M.toFunctor)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y)) _⦋n⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorPinchedSimplex.{u, max u v w, max (u + 1) v w, 0}
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M) s

lemma dgGluingNativeCommaPinchedSimplex_val :
    (dgGluingNativeCommaPinchedSimplex R C D M s).val = s.val.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorPinchedSimplex_val _ _

lemma dgGluingNativePinchedAugmentationComponent
    (J : Finset (Fin (n + 1))) (p : ℤ) (hJ : J.Nonempty) (hp : p = 1 - (J.card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R D (RightModule R C) M.toFunctor
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y) p
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData (dgGluingNativeCommaPinchedSimplex R C D M s)).component J p hJ hp) =
      (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R X.left (M.rightAt Y.right)).inv.f (p - 1)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y).v p (p - 1) (by omega)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J p hJ hp)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorPinchedSimplex_component.{u, max u v w, max (u + 1) v w, 0}
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M) s J p hJ hp
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData (dgGluingNativeCommaPinchedSimplex R C D M s)).component J p hJ hp =
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).map X Y).f p ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J p hJ hp) at h
  rw [h]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeAugmentationHomotopyComponent R C D M X Y p _

lemma dgGluingNativePinchedPrismRightCorrection_primitive
    (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPrismRightCorrection R D (RightModule R C) M.toFunctor
        (dgGluingNativeCommaPinchedSimplex R C D M s).val.toSimplexData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J)
        (Fin.last (n + 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second J hJ).castSucc (Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨_, (Finset.mem_erase.mp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second_mem_erase J hJ)).2, rfl⟩)) (Fin.castSucc_lt_last _))
      ((((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J).filter ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second J hJ).castSucc < ·)).card : ℤ).negOnePow •
        (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R X.left (M.rightAt Y.right)).inv.f (k + 1 - 1)
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y).v (k + 1) (k + 1 - 1) (by omega)
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component (J.erase (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))) (k + 1)
              (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ _ (J.min'_mem _))
              (by
                have := Finset.card_erase_add_one (J.min'_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
                omega)))) := by
  refine (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPinchedPrismRightCorrection_linear R D (RightModule R C) M.toFunctor
    (dgGluingNativeCommaPinchedSimplex R C D M s) J hJ k hk).trans ?_
  apply heq_of_eq
  exact congrArg (fun z =>
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J).filter ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second J hJ).castSucc < ·)).card : ℤ).negOnePow • z)
    (dgGluingNativePinchedAugmentationComponent R C D M s _ (k + 1) _ _)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
