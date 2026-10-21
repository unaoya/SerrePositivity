module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeHomSpanNaturality
public import SerrePositivity.InfinityCategories.Core.EquivalencePathIso

/-!
概要：同じ底変換比較 Hom の一射影に、元の射影を厳密に戻す切断を取る。
方針：射影の全境界の持ち上げから切断を取り、射影との合成の等式で同値性を示す。
規約：比較の元の共通 Hom と一射影を保つ。
使われ方：両側の分類 Hom の比較を、元の作用に整合する実際の射へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 元の一射影を厳密に戻す、同じ共通 Hom への切断。 -/
def cocartesianBaseChangeHomSpanOneSection :
    intervalMappingSpace
      (functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom))
      (functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom)) ⟶
      cocartesianBaseChangeHomComparisonSpace k p q := by
  have : TrivialKanFibration (cocartesianBaseChangeHomSpanOne k p q) :=
    cocartesianBaseChangeHomSpanOne_trivialKanFibration k p q
  exact Classical.choose (trivialKanFibration_exists_section (cocartesianBaseChangeHomSpanOne k p q))

/-- 同じ切断と元の一射影との合成は厳密に恒等射。 -/
lemma cocartesianBaseChangeHomSpanOneSection_projection :
    cocartesianBaseChangeHomSpanOneSection k p q ≫ cocartesianBaseChangeHomSpanOne k p q =
      𝟙 _ := by
  have : TrivialKanFibration (cocartesianBaseChangeHomSpanOne k p q) :=
    cocartesianBaseChangeHomSpanOne_trivialKanFibration k p q
  exact Classical.choose_spec
    (trivialKanFibration_exists_section (cocartesianBaseChangeHomSpanOne k p q))

/-- 元の射影を厳密に戻す同じ切断も、元の Hom の同値。 -/
lemma cocartesianBaseChangeHomSpanOneSection_isQCatEquivalence :
    IsQCatEquivalence (cocartesianBaseChangeHomSpanOneSection k p q) := by
  have : TrivialKanFibration (cocartesianBaseChangeHomSpanOne k p q) :=
    cocartesianBaseChangeHomSpanOne_trivialKanFibration k p q
  apply (isQCatEquivalence_of_trivialKanFibration
    (cocartesianBaseChangeHomSpanOne k p q)).cancel_right
  rw [cocartesianBaseChangeHomSpanOneSection_projection]
  exact (QCatEquivalence.refl _).isQCatEquivalence

end SerrePositivity.InfinityCategories
