module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Core.InternalHomSwap

/-! # 二重内部 Hom の第二添字の評価
概要：二重内部 Hom の交換と第二添字の評価を照合する。
方針：パラメーターの制限と定値単体の自然性を使う。
規約：任意の単体集合。使われ方：S 構成と cofiber の交換の各角の厳密な式。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 内部 Hom の交換の後の第二添字の評価は、交換前の内部 Hom の後合成。 -/
lemma internalHomSwap_evaluate_right (A B C : SSet.{u}) (b : B.obj (Opposite.op ⦋0⦌)) :
    (internalHomSwapIso A B C).hom ≫ evaluateFunctorAt (Y := (ihom A).obj C) b =
      (ihom A).map (evaluateFunctorAt (Y := C) b) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro e α
  apply ConcreteCategory.hom_ext
  intro a
  change (F.app e (𝟙 d ≫ α) a).app e (𝟙 e)
      (B.map α (PinchedHom.constant b d.unop.len)) =
    (F.app e α a).app e (𝟙 e) (PinchedHom.constant b e.unop.len)
  rw [Category.id_comp]
  exact congrArg (fun z => (F.app e α a).app e (𝟙 e) z)
    (PinchedHom.constant_pullback b α.unop)

/-- 二重内部 Hom の添字を二回交換すると元の図式を厳密に回収する。 -/
lemma internalHomSwap_twice (A B C : SSet.{u}) :
    (internalHomSwapIso A B C).hom ≫ (internalHomSwapIso B A C).hom = 𝟙 _ := by
  have hp : (pre (β_ A B).hom).app C ≫ (pre (β_ B A).hom).app C = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← pre_map, SymmetricCategory.symmetry, pre_id]
    rfl
  suffices ihomUncurry B A C ≫ (pre (β_ A B).hom).app C ≫
      (pre (β_ B A).hom).app C ≫ ihomCurry B A C = 𝟙 _ by
    simpa [internalHomSwapIso] using this
  rw [← Category.assoc ((pre (β_ A B).hom).app C) ((pre (β_ B A).hom).app C)
    (ihomCurry B A C), hp, Category.id_comp, ihomUncurry_ihomCurry]

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.internalHomSwap_evaluate_right := _root_.SerrePositivity.InfinityCategories.Kan.internalHomSwap_evaluate_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.internalHomSwap_twice := _root_.SerrePositivity.InfinityCategories.Kan.internalHomSwap_twice
