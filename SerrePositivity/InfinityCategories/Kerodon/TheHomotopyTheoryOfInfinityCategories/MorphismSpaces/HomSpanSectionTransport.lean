module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport

/-!
概要：同じ Hom 比較 span の指定された切断による輸送と共通の始域との整合性。
方針：射影の充満忠実性で切断後の合成を恒等関手へ戻す。
規約：指定された元の切断を保持する。
使われ方：元の比較三角形を使う Hom 輸送の合成則。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

variable {P X Y H : SSet.{u}} [Quasicategory P] [Quasicategory X]
  [Quasicategory Y] [Quasicategory H]
  (p : P ⟶ X) (q : P ⟶ Y) (s : X ⟶ P) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful p) (hs : s ≫ p = 𝟙 X)

/-- 充満忠実な射影の元の切断で戻す合成は、同じ span 上の恒等写像と関手同型。 -/
def homSpanSectionSourceIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p ≫ s) (𝟙 P) := by
  apply hp.preimageFunctorIso
  simpa only [Category.assoc, hs, Category.comp_id, Category.id_comp] using
    (Iso.refl (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)))

/-- 同じ span の切断による輸送を、共通の元の始域へ戻す比較。 -/
def homSpanSectionTransportFactorIso (r : H ⟶ P) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((r ≫ p) ≫ (s ≫ q)) (r ≫ q) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp ((homSpanSectionSourceIso p s hp hs).postcomp q) r)
    (by simp only [Category.assoc]) (by rw [Category.id_comp])

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
