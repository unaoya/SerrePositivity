module

public import SerrePositivity.KST.LocalizingInvariants.CofiberZeroTargetComparison
public import SerrePositivity.KST.LocalizingInvariants.LaxCAdjunction
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceExact

/-!
概要：差の実関手と C 包含の合成は、元の p の後の suspension と全関手として同型。
方針：C 包含の指定矢印の零終点と厳密な始点を使い、cofiber の選択を比較する。
規約：元の cofiber と全単体の包含を保持。使われ方：Tamme の C 軸の符号。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

lemma fromC_laxArrow_target_zero (x : C.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow (((LaxInclusion.fromC p q) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p.hom q.hom).app
      (Opposite.op ⦋0⦌) x) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((((LaxInclusion.fromC p q) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p.hom q.hom) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app (Opposite.op ⦋0⦌) x)
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow_target, ← Category.assoc]
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((LaxInclusion.fromC p q ≫ (laxSnd p q).hom) ≫ q.hom).app _ x)
  rw [LaxInclusion.fromC_snd]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroD_post q x

lemma fromC_laxArrow_source :
    ((LaxInclusion.fromC p q) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p.hom q.hom) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = p.hom := by
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow_source, ← Category.assoc]
  change (LaxInclusion.fromC p q ≫ (laxFst p q).hom) ≫ p.hom = p.hom
  rw [LaxInclusion.fromC_fst, Category.id_comp]

def fromC_differenceIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (LaxInclusion.fromC p q ≫ laxDifference p q)
    (p.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map E.obj) := by
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p.hom q.hom
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (LaxInclusion.fromC p q ≫ laxDifference p q)
      ((LaxInclusion.fromC p q ≫ a) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber E.obj (𝟙 _)) := by
    simpa only [laxDifference, Category.assoc] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (CofiberFamily.compositionIso E.obj a) (LaxInclusion.fromC p q)
  have e := (CofiberFamily.compositionIso E.obj (LaxInclusion.fromC p q ≫ a)).symm ≪≫
    cofiberZeroTargetIso E.obj _ (fromC_laxArrow_target_zero p q)
  rw [fromC_laxArrow_source] at e
  exact h ≪≫ e

end SerrePositivity.KST.LocalizingInvariants
