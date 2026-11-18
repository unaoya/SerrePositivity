module

public import SerrePositivity.InfinityCategories.Sheaves.PresheafRelativeCechColimit
public import SerrePositivity.InfinityCategories.Sheaves.PresheafRelativeCechLocalDiagonal
public import SerrePositivity.InfinityCategories.Sheaves.SetLocalEquivalence
public import Mathlib.CategoryTheory.Subfunctor.Image

/-!
概要：元の前層の射を、Mathlib の同じ像への全射と同じ包含へ分け、Čech 解消へ接続する。
方針：既存 toRange_ι の等式と、局所単射・局所全射の既存の合成の法則を使う。
規約：HTT 6.2.2.6 の局所性への通常圏の入力。局所全射を各点全射と仮定しない。
使われ方：S8 の一般の局所同値。各点全射なのは像への射だけ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u}

/-- 同じ像への射は、各点で全射。 -/
lemma toRange_app_surjective (f : P ⟶ Q) (X : Cᵒᵖ) :
    Function.Surjective ((Subfunctor.toRange f).app X) := by
  rintro ⟨x, hx⟩
  obtain ⟨p, rfl⟩ := hx
  exact ⟨p, rfl⟩

/-- 元の局所単射性は、同じ像への射にも成り立つ。 -/
lemma toRange_isLocallyInjective (J : GrothendieckTopology C) (f : P ⟶ Q)
    [CategoryTheory.Presheaf.IsLocallyInjective J f] :
    CategoryTheory.Presheaf.IsLocallyInjective J (Subfunctor.toRange f) :=
  CategoryTheory.Presheaf.isLocallyInjective_of_isLocallyInjective_fac J
    (Subfunctor.toRange_ι f)

/-- 元の局所全射性は、同じ像の包含にも成り立つ。 -/
lemma rangeInclusion_isLocallySurjective (J : GrothendieckTopology C) (f : P ⟶ Q)
    [CategoryTheory.Presheaf.IsLocallySurjective J f] :
    CategoryTheory.Presheaf.IsLocallySurjective J (Subfunctor.range f).ι :=
  CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
    (Subfunctor.toRange_ι f)

/-- 元の像への全射の同じ Čech 増大は、空間値前層の余極限余錐。 -/
lemma rangeCechCocone_isColimit (f : P ⟶ Q) :
    IsColimitCone (discretePresheafCocone (relativeCechCocone (Subfunctor.toRange f))) :=
  presheafRelativeCechCocone_isColimit (Subfunctor.toRange f) (toRange_app_surjective f)

/-- 元の局所単射性から、像への Čech 対角の全次数の局所全射性を得る。 -/
lemma rangeCechDiagonal_isLocallySurjective (J : GrothendieckTopology C) (f : P ⟶ Q)
    [CategoryTheory.Presheaf.IsLocallyInjective J f]
    (j : AsSmall.{u} SimplexCategoryᵒᵖ) :
    CategoryTheory.Presheaf.IsLocallySurjective J
      ((relativeCechDiagonal (Subfunctor.toRange f)).app j) := by
  letI := toRange_isLocallyInjective J f
  infer_instance

end SerrePositivity.InfinityCategories.Sheaves
