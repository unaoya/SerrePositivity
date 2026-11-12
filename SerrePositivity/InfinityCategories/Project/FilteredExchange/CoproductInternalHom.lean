module
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic


/-!
概要：二項直和を始域とする内部 Hom の、二つの指定射への制限と貼り合わせ。
方針：右直積の直和保存を使って uncurry した二射を貼る。
規約：全パラメータで厳密に制限を保持する。
使われ方：filtered な底の二項対角関手の cofinality。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：二項直和の内部 Hom の左側への制限。
方針：右直積による直和の比較の左脚を計算する。
規約：全パラメータ。使われ方：uncurry した射の貼り合わせ。 -/
lemma tensorCoprod_inl (A B T : SSet.{u}) :
    (coprod.inl : A ⊗ T ⟶ (A ⊗ T) ⨿ (B ⊗ T)) ≫
      (PreservesColimitPair.iso (tensorRight T) A B).hom =
        (coprod.inl : A ⟶ A ⨿ B) ▷ T := by
  change coprod.inl ≫ coprodComparison (tensorRight T) A B = _
  simp [coprodComparison]

/-- 概要：二項直和の内部 Hom の右側への制限。
方針：右直積による直和の比較の右脚を計算する。
規約：全パラメータ。使われ方：uncurry した射の貼り合わせ。 -/
lemma tensorCoprod_inr (A B T : SSet.{u}) :
    (coprod.inr : B ⊗ T ⟶ (A ⊗ T) ⨿ (B ⊗ T)) ≫
      (PreservesColimitPair.iso (tensorRight T) A B).hom =
        (coprod.inr : B ⟶ A ⨿ B) ▷ T := by
  change coprod.inr ≫ coprodComparison (tensorRight T) A B = _
  simp [coprodComparison]

/-- 概要：二つの内部 Hom への指定射を、直和の内部 Hom への一射に貼る。
方針：uncurry した射の直和を直積の比較同型で移す。
規約：全形状で定義。使われ方：内部 Hom の直和から積への同型の逆射。 -/
def coproductFunctorGlue {A B T X : SSet.{u}}
    (f : T ⟶ (ihom A).obj X) (g : T ⟶ (ihom B).obj X) :
    T ⟶ (ihom (A ⨿ B)).obj X :=
  curry ((PreservesColimitPair.iso (tensorRight T) A B).inv ≫
    coprod.desc (uncurry f) (uncurry g))

/-- 概要：貼り合わせの左制限は元の射。
方針：curry と前合成、直和の左脚の式を使う。
規約：厳密な等式。使われ方：積表示の逆射の検証。 -/
lemma coproductFunctorGlue_inl {A B T X : SSet.{u}}
    (f : T ⟶ (ihom A).obj X) (g : T ⟶ (ihom B).obj X) :
    coproductFunctorGlue f g ≫ (pre (coprod.inl : A ⟶ A ⨿ B)).app X = f := by
  apply uncurry_injective
  rw [uncurry_pre_app, coproductFunctorGlue, uncurry_curry,
    ← tensorCoprod_inl, Category.assoc, Iso.hom_inv_id_assoc, coprod.inl_desc]

/-- 概要：貼り合わせの右制限は元の射。
方針：curry と前合成、直和の右脚の式を使う。
規約：厳密な等式。使われ方：積表示の逆射の検証。 -/
lemma coproductFunctorGlue_inr {A B T X : SSet.{u}}
    (f : T ⟶ (ihom A).obj X) (g : T ⟶ (ihom B).obj X) :
    coproductFunctorGlue f g ≫ (pre (coprod.inr : B ⟶ A ⨿ B)).app X = g := by
  apply uncurry_injective
  rw [uncurry_pre_app, coproductFunctorGlue, uncurry_curry,
    ← tensorCoprod_inr, Category.assoc, Iso.hom_inv_id_assoc, coprod.inr_desc]

/-- 概要：直和の内部 Hom への射は二つの制限で決まる。
方針：uncurry し、右直積の直和表示へ戻して両脚で検査する。
規約：全パラメータ。使われ方：内部 Hom の積同型の検証。 -/
lemma coproductFunctor_hom_ext {A B T X : SSet.{u}}
    {f g : T ⟶ (ihom (A ⨿ B)).obj X}
    (h : f ≫ (pre (coprod.inl : A ⟶ A ⨿ B)).app X =
      g ≫ (pre (coprod.inl : A ⟶ A ⨿ B)).app X)
    (k : f ≫ (pre (coprod.inr : B ⟶ A ⨿ B)).app X =
      g ≫ (pre (coprod.inr : B ⟶ A ⨿ B)).app X) : f = g := by
  apply uncurry_injective
  apply (cancel_epi (PreservesColimitPair.iso (tensorRight T) A B).hom).1
  apply coprod.hom_ext
  · rw [← Category.assoc, tensorCoprod_inl, ← uncurry_pre_app,
      ← Category.assoc, tensorCoprod_inl, ← uncurry_pre_app]
    exact congrArg uncurry h
  · rw [← Category.assoc, tensorCoprod_inr, ← uncurry_pre_app,
      ← Category.assoc, tensorCoprod_inr, ← uncurry_pre_app]
    exact congrArg uncurry k

end SerrePositivity.InfinityCategories.Project.FilteredExchange
