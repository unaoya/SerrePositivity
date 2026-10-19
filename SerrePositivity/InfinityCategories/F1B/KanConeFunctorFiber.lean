module

public import SerrePositivity.InfinityCategories.F1B.KanNerveConeEquiv
public import SerrePositivity.InfinityCategories.F1B.KanConeExtensionHom
public import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-!
概要：通常の錐を固定図式上の拡張関手の fiber へ写す。
方針：拡張関手と図式上で恒等な自然変換の復元を使う。
規約：同じ宇宙の小さい圏と単体集合を扱う。
使われ方：B5 の通常の錐と native な錐の族の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

/-- 概要：拡張関手を元の添字へ制限する関手。
方針：拡張関手と図式上で恒等な自然変換の復元を使う。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
abbrev kanConeRestrictionFunctor :=
  (Functor.whiskeringLeft I (WithInitial I) C).obj WithInitial.incl

/-- 概要：通常の錐を指定図式上の関手の fiber へ写す関手。
方針：拡張関手と図式上で恒等な自然変換の復元を使う。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
def kanConeFiberFunctor : Cone F ⥤ Functor.Fiber (kanConeRestrictionFunctor (I := I) (C := C)) F :=
  Functor.Fiber.inducedFunctor (kanConeExtensionFunctor_restrict (F := F))

/-- 概要：fiber の射は元の図式上で恒等な自然変換。
方針：拡張関手と図式上で恒等な自然変換の復元を使う。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
lemma kanConeFiberHom_fixed {c d : Cone F}
    (η : (kanConeFiberFunctor (F := F)).obj c ⟶ (kanConeFiberFunctor (F := F)).obj d) :
    Functor.whiskerLeft WithInitial.incl η.val = 𝟙 F := by
  have := η.property
  have h := IsHomLift.fac' (kanConeRestrictionFunctor (I := I) (C := C)) (𝟙 F) η.val
  simp only [eqToHom_refl, Category.comp_id] at h
  exact h

/-- 概要：錐から関手の fiber への関手は充満忠実。
方針：拡張関手と図式上で恒等な自然変換の復元を使う。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
def kanConeFiberFunctor_fullyFaithful : (kanConeFiberFunctor (F := F)).FullyFaithful where
  preimage {c d} η := (kanConeExtensionHomEquiv c d).symm ⟨η.val, kanConeFiberHom_fixed η⟩
  map_preimage {c d} η := by
    apply Subtype.ext
    change kanConeWithInitialNatTrans ((kanConeExtensionHomEquiv c d).symm _) = η.val
    exact congrArg Subtype.val ((kanConeExtensionHomEquiv c d).apply_symm_apply
      ⟨η.val, kanConeFiberHom_fixed η⟩)
  preimage_map {c d} f := (kanConeExtensionHomEquiv c d).symm_apply_apply f

/-- 概要：関手の fiber の各対象は通常の錐から厳密に復元できる。
方針：拡張関手と図式上で恒等な自然変換の復元を使う。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
lemma kanConeFiberFunctor_obj_surjective :
    Function.Surjective (kanConeFiberFunctor (F := F)).obj := by
  intro G
  refine ⟨kanConeFromWithInitialFunctor G.val G.property, ?_⟩
  apply Subtype.ext
  exact kanConeWithInitialFunctor_of_functor G.val G.property

end SerrePositivity.InfinityCategories.F1B
