module

public import SerrePositivity.KST.LocalizingInvariants.LocalizationFactorization

/-!
概要：同じ辺集合を局所化する二つの実射の比較は、指定した因子化関手の同値になる。
方針：逆も普遍性で下ろし、前合成の充満忠実性で両合成の実関手同型を持ち上げる。
規約：順方向は元の比較関手。使われ方：一般商候補と反射的な差の項の比較。
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

lemma localizationPre_fullyFaithful {X Q Y : SSet.{u}} [Quasicategory Q] [Quasicategory Y]
    (F : X ⟶ Q) (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre F).app Y) := by
  obtain ⟨hF, hU⟩ := hF
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι F W hF Y]
  exact (hU Y).isFullyFaithful.comp
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex X Y W))

def localizationFactorizationIso {X Q Y : SSet.{u}} [Quasicategory Q] [Quasicategory Y]
    (F : X ⟶ Q) (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W) {K L : Q ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ K) (F ≫ L)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso K L :=
  (localizationPre_fullyFaithful F W hF).preimageVertexIso e

variable {X Q R : SSet.{u}} [Quasicategory Q] [Quasicategory R]
  (F : X ⟶ Q) (G : X ⟶ R) (W : Set (X _⦋1⦌))
  (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization G W)
  (K : Q ⟶ R) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ K) G)

def localizationComparisonInverse : R ⟶ Q := localizationDescend G W hG F hF.choose

def localizationComparisonInverseIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G ≫ localizationComparisonInverse F G W hF hG) F :=
  localizationDescendIso G W hG F hF.choose

def localizationComparisonHomInvIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (K ≫ localizationComparisonInverse F G W hF hG) (𝟙 Q) := by
  apply localizationFactorizationIso F W hF
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e (localizationComparisonInverse F G W hF hG) ≪≫
    localizationComparisonInverseIso F G W hF hG
  simpa only [Category.assoc, Category.comp_id] using h

def localizationComparisonInvHomIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (localizationComparisonInverse F G W hF hG ≫ K) (𝟙 R) := by
  apply localizationFactorizationIso G W hG
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (localizationComparisonInverseIso F G W hF hG) K ≪≫ e
  simpa only [Category.assoc, Category.comp_id] using h

/-- 同じ辺集合の局所化を比較する元の関手は、実際の逆と両合成の同型を持つ。 -/
def localizationComparisonEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Q R where
  hom := K
  inv := localizationComparisonInverse F G W hF hG
  homInvIso := localizationComparisonHomInvIso F G W hF hG K e
  invHomIso := localizationComparisonInvHomIso F G W hF hG K e

end SerrePositivity.KST.LocalizingInvariants
