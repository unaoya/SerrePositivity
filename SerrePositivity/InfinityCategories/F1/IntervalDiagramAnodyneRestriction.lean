module

public import SerrePositivity.InfinityCategories.F1.IntervalDiagramRestriction
public import SerrePositivity.InfinityCategories.F1.IntervalMappingPostEquivalence
public import SerrePositivity.InfinityCategories.Core.InnerAnodyneEquivalence

/-!
概要：inner anodyne な底の包含への、元の区間 Hom の制限は自明 Kan fibration。
方針：通常の関手空間の自明 Kan 制限を、同じ端点を固定する区間 Hom へ移す。
規約：元の区間制限写像そのものについて述べる。
使われ方：高次単体とその spine の分類先の Hom を比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- inner anodyne な底の包含への、同じ両端固定区間 Hom の制限は自明 Kan。 -/
lemma intervalDiagramRestriction_trivialKanFibration_of_innerAnodyne
    {A B X : SSet.{u}} [Quasicategory X] (i : A ⟶ B) (hi : innerAnodyneExtensions i)
    (F G : B ⟶ X) : TrivialKanFibration (intervalDiagramRestriction i F G) := by
  letI := trivialKanFibration_pre_of_innerAnodyne i hi X
  exact intervalMappingPostOfEq_trivialKanFibration _ _ _ _ _

/-- 同じ inner anodyne な底への区間 Hom の制限は、元の射として同値。 -/
lemma intervalDiagramRestriction_isQCatEquivalence_of_innerAnodyne
    {A B X : SSet.{u}} [Quasicategory X] (i : A ⟶ B) (hi : innerAnodyneExtensions i)
    (F G : B ⟶ X) : IsQCatEquivalence (intervalDiagramRestriction i F G) := by
  letI := intervalDiagramRestriction_trivialKanFibration_of_innerAnodyne i hi F G
  exact isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories
