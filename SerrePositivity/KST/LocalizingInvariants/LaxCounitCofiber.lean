module

public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyExactComparison
public import SerrePositivity.KST.LocalizingInvariants.CofiberZeroSourceComparison
public import SerrePositivity.KST.LocalizingInvariants.LaxDAdjunction

/-!
概要：元の D 包含の随伴余単位の cofiber を全族として選び、第一射影を同定する。
方針：元の余単位を矢印族にし、完全射影と零始点 cofiber の自然比較を合成する。
規約：随伴や cofiber を入力に追加しない。使われ方：一般商の二脚の coherent な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxCounit
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

def arrow : (laxCategory p q).obj ⟶ (ihom (Δ[1] : SSet.{u})).obj (laxCategory p q).obj :=
  ZeroArrowFamily.ofHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy (LaxInclusion.fromDAdjunction p q).counitHom)

lemma arrow_source : arrow p q ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      (laxSnd p q).hom ≫ LaxInclusion.fromD p q :=
  ZeroArrowFamily.ofHomotopy_source _

lemma arrow_target : arrow p q ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = 𝟙 (laxCategory p q).obj :=
  ZeroArrowFamily.ofHomotopy_target _

instance arrow_isExact : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (arrow p q) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (arrow p q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
    rw [arrow_source]; infer_instance
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (arrow p q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    rw [arrow_target]; infer_instance
  exact arrow_exact_of_endpoints (laxCategory p q).obj _

def cofiber : (laxCategory p q).obj ⟶ (laxCategory p q).obj :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber (laxCategory p q).obj (arrow p q)

instance cofiber_isExact : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (cofiber p q) :=
  CofiberFamily.cofiber_isExact _ _

lemma fst_arrow_source_zero (x : (laxCategory p q).obj _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow
    ((arrow p q ≫ (ihom (Δ[1] : SSet.{u})).map (laxFst p q).hom).app
      (Opposite.op ⦋0⦌) x) := by
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((arrow p q ≫ (ihom (Δ[1] : SSet.{u})).map (laxFst p q).hom) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) x)
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.arrowMap_evaluation, ← Category.assoc, arrow_source,
    Category.assoc, LaxInclusion.fromD_fst]
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroC : D.obj ⟶ C.obj).app _ ((laxSnd p q).hom.app _ x))
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroC, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex C.obj).isZero

lemma fst_arrow_target :
    (arrow p q ≫ (ihom (Δ[1] : SSet.{u})).map (laxFst p q).hom) ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.target C.obj = (laxFst p q).hom := by
  change (arrow p q ≫ (ihom (Δ[1] : SSet.{u})).map (laxFst p q).hom) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.arrowMap_evaluation, ← Category.assoc, arrow_target, Category.id_comp]

def cofiber_fstIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cofiber p q ≫ (laxFst p q).hom) (laxFst p q).hom := by
  have e := cofiberZeroSourceIso C.obj
    (arrow p q ≫ (ihom (Δ[1] : SSet.{u})).map (laxFst p q).hom)
    (fst_arrow_source_zero p q)
  rw [fst_arrow_target] at e
  exact CofiberFamily.familyExactComparison (laxFst p q).hom (arrow p q) ≪≫ e

end SerrePositivity.KST.LocalizingInvariants.LaxCounit
