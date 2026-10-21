module

public import SerrePositivity.InfinityCategories.F1.FullyFaithfulPostcomposition

/-!
概要：同じ Hom 比較 span の指定された切断による輸送と共通の始域との整合性。
方針：射影の充満忠実性で切断後の合成を恒等関手へ戻す。
規約：指定された元の切断を保持する。
使われ方：元の比較三角形を使う Hom 輸送の合成則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {P X Y H : SSet.{u}} [Quasicategory P] [Quasicategory X]
  [Quasicategory Y] [Quasicategory H]
  (p : P ⟶ X) (q : P ⟶ Y) (s : X ⟶ P) (hp : IsFullyFaithful p) (hs : s ≫ p = 𝟙 X)

/-- 充満忠実な射影の元の切断で戻す合成は、同じ span 上の恒等写像と関手同型。 -/
def homSpanSectionSourceIso : FunctorIso (p ≫ s) (𝟙 P) := by
  apply hp.preimageFunctorIso
  simpa only [Category.assoc, hs, Category.comp_id, Category.id_comp] using
    (Iso.refl (SSet.HomotopyCategory.mk (functorVertex p)))

/-- 同じ span の切断による輸送を、共通の元の始域へ戻す比較。 -/
def homSpanSectionTransportFactorIso (r : H ⟶ P) :
    FunctorIso ((r ≫ p) ≫ (s ≫ q)) (r ≫ q) := by
  have e := FunctorIso.precomp ((homSpanSectionSourceIso p s hp hs).postcomp q) r
  simpa only [Category.assoc, Category.id_comp] using e

end SerrePositivity.InfinityCategories
