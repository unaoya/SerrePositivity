module

public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
public import SerrePositivity.KST.LocalizingInvariants.CofiberInverseRotationZero
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.AdjunctionCounitImage
public import SerrePositivity.KST.LocalizingInvariants.ArrowFamilyRoundTrip
public import SerrePositivity.KST.LocalizingInvariants.HomotopyPathFamily
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveLocalization

/-!
概要：普遍の恒等 lax 差への比較の第一射影は D 包含上で零となる。
方針：元の D 余単位を D 上へ制限し、可逆性と逆 cofiber 回転の fiber 判定を使う。
規約：同じ余単位と同じ逆回転を保持。使われ方：第一射影を C 商を通して分解する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
variable {C D E Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)

lemma lift_fst : lift p q r ≫ (laxFst (𝟙 Q) (𝟙 Q)).hom =
    connectingArrow p q r ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  change lift p q r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst (𝟙 Q.obj) (𝟙 Q.obj) = _
  rw [lift, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse_fst]

def first : (laxCategory p q).obj ⟶ Q.obj := lift p q r ≫ (laxFst (𝟙 Q) (𝟙 Q)).hom

instance first_isExact : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (first p q r) := by
  unfold first
  infer_instance

lemma fromD_first_zero (d : D.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((LaxInclusion.fromD p q ≫ first p q r).app (Opposite.op ⦋0⦌) d) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy (LaxInclusion.fromDAdjunction p q).counitHom
  let J := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (LaxInclusion.fromD p q)
  let K := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp J r.hom
  have hu : IsIso (LaxInclusion.fromDAdjunction p q).unitHom := by
    rw [LaxInclusion.fromDAdjunction_unit]
    infer_instance
  have hj : IsIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy J)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom]
    exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.counit_precompLeft_isIso (LaxInclusion.fromDAdjunction p q)
  have hk : IsIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy K)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom]
    infer_instance
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.homotopy_component_isInvertible_of_isIso K d
  have he : ZeroArrowFamily.ofHomotopy K = LaxInclusion.fromD p q ≫ arrow p q r := by
    rw [ZeroArrowFamily.ofHomotopy_postcomp, ZeroArrowFamily.ofHomotopy_precomp]
    rfl
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
      ((LaxInclusion.fromD p q ≫ arrow p q r).app (Opposite.op ⦋0⦌) d) := by
    rw [← he]
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge K d).toTruncated)
      (ofHomotopy_component_edge K d)).mpr
    exact hc
  have hz := CofiberRotation.inverseRotation_source_zero Q.obj _ ha
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((LaxInclusion.fromD p q ≫ arrow p q r) ≫
    CofiberRotation.inverseRotation Q.obj ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) d)
      at hz
  simpa only [first, lift_fst, connectingArrow, Category.assoc] using hz

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
