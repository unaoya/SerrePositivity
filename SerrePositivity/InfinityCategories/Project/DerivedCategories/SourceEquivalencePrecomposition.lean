module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorComposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful
/-!
概要：始域の同値を経由した前合成の充満忠実性と実延長の輸送。
方針：実前合成の合成公式と同値の単位の関手同型を使う。
規約：全関手 ∞ 圏での比較。使われ方：平坦 dg 模型による局所化の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalClosed SSet
/-- 始域の同値の逆を経由しても、全前合成の充満忠実性を保つ。 -/
lemma precomposition_isFullyFaithful_of_sourceEquivalence {R X Q Y : SSet.{u}}
    [Quasicategory R] [Quasicategory X] [Quasicategory Y]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence R X) (q : R ⟶ Q) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre q).app Y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre (e.inv ≫ q)).app Y) := by
  have hi := (e.symm.isQCatEquivalence.precompose Y).isFullyFaithful
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre e.inv).app Y) at hi
  have hc := h.comp hi
  simpa only [pre_map, NatTrans.comp_app] using hc
/-- 分解上での一つの実延長同型を、元の始域上の同じ延長同型へ輸送する。 -/
def extensionIsoOfSourceEquivalence {R X Q Y : SSet.{u}}
    [Quasicategory R] [Quasicategory X]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence R X) (q : R ⟶ Q) (F : X ⟶ Y) (G : Q ⟶ Y)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (q ≫ G) (e.hom ≫ F)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((e.inv ≫ q) ≫ G) F := by
  have h₁ := h.precomp e.inv
  have h₂ := e.invHomIso.postcomp F
  exact (by simpa only [Category.assoc, Category.id_comp] using h₁ ≪≫ h₂)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
