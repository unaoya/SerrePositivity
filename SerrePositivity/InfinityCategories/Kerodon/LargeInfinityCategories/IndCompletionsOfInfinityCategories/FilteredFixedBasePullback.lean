module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FilteredFiniteLimits
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：固定底上の filtered な pullback 図式の余極限は同じ底上の pullback。
方針：有限極限保存を適用し、定値図式の余極限の標準同型で底を元へ戻す。
規約：余極限から固定底への射は元の射の余錐から降ろした同じ射。
使われ方：right fibration の元の fiber と strict 余極限の比較。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [SmallCategory I] [IsFiltered I]

/-- filtered な定値図式の余極限を元の対象に戻す標準同型。 -/
def filteredConstantColimitIso (X : SSet.{u}) : colimit ((Functor.const I).obj X) ≅ X := by
  have : IsConnected I := IsFiltered.isConnected I
  exact (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstCocone I X)

@[reassoc (attr := simp)]
lemma filteredConstantColimitIso_ι (X : SSet.{u}) (i : I) :
    colimit.ι ((Functor.const I).obj X) i ≫ (filteredConstantColimitIso (I := I) X).hom =
      𝟙 X := colimit.comp_coconePointUniqueUpToIso_hom _ _

/-- 同じ定値図式への射から、元の固定底への射を降ろす。 -/
def fixedBaseColimitMap {F : I ⥤ SSet.{u}} {B : SSet.{u}}
    (η : F ⟶ (Functor.const I).obj B) : colimit F ⟶ B :=
  colimit.desc F { pt := B, ι := η }

omit [IsFiltered I] in
@[reassoc (attr := simp)]
lemma fixedBaseColimitMap_ι {F : I ⥤ SSet.{u}} {B : SSet.{u}}
    (η : F ⟶ (Functor.const I).obj B) (i : I) :
    colimit.ι F i ≫ fixedBaseColimitMap η = η.app i := colimit.ι_desc _ _

/-- 定値底への余極限射は標準同型を通す同じ通常の余極限射。 -/
lemma fixedBaseColimitMap_eq {F : I ⥤ SSet.{u}} {B : SSet.{u}}
    (η : F ⟶ (Functor.const I).obj B) :
    colim.map η ≫ (filteredConstantColimitIso (I := I) B).hom = fixedBaseColimitMap η := by
  apply colimit.hom_ext
  intro i
  simp

/-- 各段で同じ固定底上の pullback なら、その同じ余極限正方形も pullback。 -/
lemma filteredFixedBaseColimit_isPullback
    {F G : I ⥤ SSet.{u}} {A B : SSet.{u}} (α : F ⟶ G)
    (β : F ⟶ (Functor.const I).obj A) (γ : G ⟶ (Functor.const I).obj B)
    (f : A ⟶ B) (h : ∀ i, IsPullback (α.app i) (β.app i) (γ.app i) f) :
    IsPullback (colim.map α) (fixedBaseColimitMap β) (fixedBaseColimitMap γ) f := by
  let δ : (Functor.const I).obj A ⟶ (Functor.const I).obj B := (Functor.const I).map f
  have hs : IsPullback α β γ δ := IsPullback.of_forall_isPullback_app h
  have hm := hs.map (colim : (I ⥤ SSet.{u}) ⥤ SSet.{u})
  apply hm.of_iso (Iso.refl _) (Iso.refl _)
    (filteredConstantColimitIso A) (filteredConstantColimitIso B)
  · simp
  · simpa only [Iso.refl_hom, Category.id_comp] using fixedBaseColimitMap_eq β
  · simpa only [Iso.refl_hom, Category.id_comp] using fixedBaseColimitMap_eq γ
  · apply colimit.hom_ext
    intro i
    simp [δ]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
