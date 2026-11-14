module
public import SerrePositivity.KST.SConstruction.CofiberMaps

/-! # cofiber 保存条件による後合成の関手法則
概要：同じ S_n への cofiber 保存型の後合成は恒等・合成・単体作用と厳密に可換。
方針：gapped 包含の単射で通常の内部 Hom の関手法則へ戻す。
規約：証明の選択は proof irrelevance で消える。使われ方：反復の全構造射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：cofiber 保存型の後合成は恒等射を保つ。
方針：包含後に内部 Hom の恒等法則を適用する。
規約：厳密な等号。使われ方：反復関手の恒等法則。 -/
lemma sPostcompCofiber_id (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    sPostcompCofiber n (𝟙 C) (preservesCofiberData_id C) = 𝟙 (sConstruction n C) := by
  apply (cancel_mono (gappedSubcomplex n C).ι).1
  erw [sPostcompCofiber_ι, CategoryTheory.Functor.map_id]

/-- 概要：cofiber 保存型の後合成は射の合成を保つ。
方針：包含後に内部 Hom の合成法則を適用する。
規約：厳密な等号。使われ方：反復関手の合成法則。 -/
lemma sPostcompCofiber_comp (n : ℕ) {C D E : SSet.{u}} [Quasicategory D] [Quasicategory E]
    (f : C ⟶ D) (g : D ⟶ E) (hf : PreservesCofiberData f) (hg : PreservesCofiberData g) :
    sPostcompCofiber n (f ≫ g) (PreservesCofiberData.comp hf hg) =
      sPostcompCofiber n f hf ≫ sPostcompCofiber n g hg := by
  apply (cancel_mono (gappedSubcomplex n E).ι).1
  rw [sPostcompCofiber_ι, CategoryTheory.Functor.map_comp, Category.assoc, sPostcompCofiber_ι]
  simp only [← Category.assoc]
  erw [sPostcompCofiber_ι]

/-- 概要：cofiber 保存型の後合成は面・退化写像と可換。
方針：包含後で内部 Hom の前合成と後合成の自然性を使う。
規約：全単体での厳密な可換性。使われ方：単体的自己関手の自然性。 -/
lemma sPostcompCofiber_sMap {m n : ℕ} {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) (θ : Fin (m + 1) →o Fin (n + 1)) :
    sPostcompCofiber n f hf ≫ sMap D θ = sMap C θ ≫ sPostcompCofiber m f hf := by
  apply (cancel_mono (gappedSubcomplex m D).ι).1
  rw [Category.assoc, sMap_ι, ← Category.assoc, sPostcompCofiber_ι,
    Category.assoc, (pre (arNerveMap θ)).naturality]
  symm
  rw [Category.assoc, sPostcompCofiber_ι, ← Category.assoc, sMap_ι, Category.assoc]

/-- 概要：cofiber 保存型の後合成は零図式を像の零図式へ厳密に送る。
方針：包含後に定値図式の後合成を計算する。
規約：任意の零対象で成り立つ。使われ方：多単体構造の基点。 -/
lemma sPostcompCofiber_zeroVertex (n : ℕ) {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) (z : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) :
    (sPostcompCofiber n f hf).app (Opposite.op ⦋0⦌) (sConstructionZeroVertex n z hz) =
      sConstructionZeroVertex n (f.app (Opposite.op ⦋0⦌) z) (hf.1 z hz) := by
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.const z : arNerve n ⟶ C) ≫ f) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (f.app (Opposite.op ⦋0⦌) z) : arNerve n ⟶ D)
  rw [SSet.const_comp]

end SerrePositivity.KST.SConstruction
