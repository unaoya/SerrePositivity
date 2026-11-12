module
public import SerrePositivity.KST.NonConnective.DGKInputIndExtension
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FilteredGeometricFunctorOperations
public import SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.EquivalenceColimits

/-!
概要：固定 ν 値間の実同値を、元の同じ Indω 間の実同値へ延長する。
方針：指定順逆射の Yoneda 族を同じ制限同値で延長し、二つの逆二胞体を制限から反映する。
規約：一般の Ind API は複製せず固定 dg ν 値に特殊化。D-8 の cone 比較は別工程。
使われ方：K-7 d4・e の Morita 同値と Ind 模型の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective

local instance indEquivalenceRegular : Fact (Cardinal.aleph0.{w}).IsRegular :=
  Cardinal.fact_isRegular_aleph0
variable (R : Type u) [CommRing R] (A B : PerfDGInput.{u, v} R)
  (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj (dgKInputStableValue R A).obj)
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj (dgKInputStableValue R B).obj))

/-- 同じ ν の指定順逆射から得た、元の二つの Indω の実同値。 -/
def dgKInputIndEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (dgKInputIndCompletion R A)
    (dgKInputIndCompletion R B) := by
  let YA := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj
  let YB := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R B).obj
  let F := dgKInputIndExtension R A B (e.hom ≫ YB)
  let G := dgKInputIndExtension R B A (e.inv ≫ YA)
  have hF := dgKInputIndExtension_preservesFilteredColimits R A B (e.hom ≫ YB)
  have hG := dgKInputIndExtension_preservesFilteredColimits R B A (e.inv ≫ YA)
  have hFG := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservesSmallFilteredColimits_comp hF hG
  have hGF := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservesSmallFilteredColimits_comp hG hF
  have hA := _root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits Cardinal.aleph0
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (Iso.refl (dgKInputIndCompletion R A))).isQCatEquivalence
  have hB := _root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits Cardinal.aleph0
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (Iso.refl (dgKInputIndCompletion R B))).isQCatEquivalence
  have eF := dgKInputIndExtension_restrictionIso R A B (e.hom ≫ YB)
  have eG := dgKInputIndExtension_restrictionIso R B A (e.inv ≫ YA)
  have rA₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (YA ≫ (F ≫ G)) (e.hom ≫ YB ≫ G) := by
    simpa only [Category.assoc] using! eF.postcomp G
  have rA₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (e.hom ≫ YB ≫ G) (e.hom ≫ e.inv ≫ YA) := eG.precomp e.hom
  have rA₃ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (e.hom ≫ e.inv ≫ YA) YA := by
    simpa only [Category.assoc, Category.id_comp] using! e.homInvIso.postcomp YA
  have rB₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (YB ≫ (G ≫ F)) (e.inv ≫ YA ≫ F) := by
    simpa only [Category.assoc] using! eG.postcomp F
  have rB₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (e.inv ≫ YA ≫ F) (e.inv ≫ e.hom ≫ YB) := eF.precomp e.inv
  have rB₃ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (e.inv ≫ e.hom ≫ YB) YB := by
    simpa only [Category.assoc, Category.id_comp] using! e.invHomIso.postcomp YB
  refine ⟨F, G, dgKInputIndFunctorIso_of_restriction R A A (F ≫ G) (𝟙 _) hFG hA ?_,
    dgKInputIndFunctorIso_of_restriction R B B (G ≫ F) (𝟙 _) hGF hB ?_⟩
  · simpa only [Category.comp_id] using! rA₁ ≪≫ rA₂ ≪≫ rA₃
  · simpa only [Category.comp_id] using! rB₁ ≪≫ rB₂ ≪≫ rB₃

/-- 順射は元の指定順射と同じ Yoneda を、同じ制限同値で延長した実関手。 -/
theorem dgKInputIndEquivalence_hom :
    (dgKInputIndEquivalence R A B e).hom = dgKInputIndExtension R A B
      (e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R B).obj) := rfl

end SerrePositivity.KST.NonConnective
