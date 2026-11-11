module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.LaxDifferenceNullComposite

public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyZeroTriangle
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceUnitD

/-!
概要：元の lax 矢印と元の cofiber 射の合成は h Fun で零である。
方針：関手圏内の零角四角形の二辺を元の二つの代表に端点ごと比較する。
規約：各対象での零性ではなく自然変換全体の等式。使われ方：実随伴単位の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
attribute [local instance] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.laxDifferenceFunctorZero _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.laxDifferenceFunctorZeroMorphisms

variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
/-- 元の指定矢印族の h Fun の類。 -/
def laxArrowHom : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom ((laxFst p q).hom ≫ p.hom) ((laxSnd p q).hom ≫ q.hom) :=
  Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (laxArrowHomotopy p q))

lemma laxDifferenceNullComposite : laxArrowHom p q ≫ laxDifferenceProjectionHom p q =
    (0 : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom ((laxFst p q).hom ≫ p.hom) (laxDifference p q)) := by
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p.hom q.hom
  let t := CofiberFamily.functorZeroTriangle E.obj a
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.comp_zero_of_arrowMk_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom t.square) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight t.square)
  · apply Truncated.HomotopyCategory.congr_arrowMk_homMk
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow_edge]
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫
      diagramFamilyTranspose (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.squares E.obj a)) = _
    rw [diagramFamilyTranspose_pre, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.squares_bottom]
    rfl
  · apply Truncated.HomotopyCategory.congr_arrowMk_homMk
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow_edge]
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫
      diagramFamilyTranspose (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.squares E.obj a)) = _
    rw [diagramFamilyTranspose_pre]
    have he : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.squares E.obj a ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge).app E.obj =
        CofiberDiagrams.lift E.obj a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right E.obj := by
      rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right, ← Category.assoc, CofiberDiagrams.lift_inclusion]
    rw [he]
    rfl
  · exact CofiberFamily.functorZeroTriangle_comp_zero E.obj a

/-- 可逆な実余単位で相殺すると、D 成分を q で写した射との合成も零になる。 -/
lemma laxDifferenceUnitD_nullComposite {v : E.obj ⟶ D.obj}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction q.hom v) (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful v) :
    laxArrowHom p q ≫
        (hoFunctor.map ((ihom (laxCategory p q).obj).map q.hom)).toFunctor.map
          (laxDifferenceUnitD p q a) =
      (0 : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom ((laxFst p q).hom ≫ p.hom) (laxDifference p q ≫ v ≫ q.hom)) := by
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.fullyFaithfulRightAdjunction_counitHom_isIso q v a hv
  let ε := (hoFunctor.map ((pre (laxDifference p q)).app E.obj)).toFunctor.map a.counitHom
  have : IsIso ε := inferInstance
  apply (cancel_mono ε).1
  rw [Category.assoc, laxDifferenceUnitD_counit, laxDifferenceNullComposite, zero_comp]

end SerrePositivity.KST.LocalizingInvariants
