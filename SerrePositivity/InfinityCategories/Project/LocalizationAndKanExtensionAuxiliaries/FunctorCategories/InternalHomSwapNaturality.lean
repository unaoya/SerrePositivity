module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InternalHomSwap
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：二重内部 Hom の交換と前後合成の整合性。
方針：交換の成分を計算し、逆同型の式は同型の消去で導く。
規約：対象と射に充填性を仮定しない。
使われ方：境界の相対内部 Hom と相対余錐制限を交換する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：二重内部 Hom の交換は標的への後合成と可換。
方針：二つの内部 Hom の成分で同じ後合成を計算する。
規約：標的の射は任意。
使われ方：相対比較の標的成分の整合性。 -/
lemma internalHomSwap_postcomp (A B : SSet.{u}) {D E : SSet.{u}} (p : D ⟶ E) :
    (ihom A).map ((ihom B).map p) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A B E).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A B D).hom ≫ (ihom B).map ((ihom A).map p) := by
  rfl

/-- 概要：二重内部 Hom の交換は第一始域への前合成と可換。
方針：第一始域の制限を交換後の第二内部 Hom に移す。
規約：始域の射は任意。
使われ方：相対比較の境界成分の整合性。 -/
lemma internalHomSwap_pre_left {A₀ A : SSet.{u}} (i : A₀ ⟶ A) (B D : SSet.{u}) :
    (pre i).app ((ihom B).obj D) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A₀ B D).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A B D).hom ≫ (ihom B).map ((pre i).app D) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro e α
  apply ConcreteCategory.hom_ext
  intro b
  apply CategoryTheory.Functor.functorHom_ext
  intro t β
  apply ConcreteCategory.hom_ext
  intro a
  change (F.app t (α ≫ β) (i.app t a)).app t (𝟙 t) (B.map β b) =
    (F.app t (α ≫ β) (i.app t a)).app t (𝟙 t) (B.map (β ≫ 𝟙 t) b)
  rw [Category.comp_id]

/-- 概要：二つの内部 Hom の順序を二度交換すると恒等射に戻る。
方針：二重の評価を計算し、元の単体の自然性で戻す。
規約：交換後に同じ標的を使う。
使われ方：相対内部 Hom の順序交換の逆射の構成。 -/
lemma internalHomSwap_hom_hom (A B D : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A B D).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso B A D).hom =
      𝟙 ((ihom A).obj ((ihom B).obj D)) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro e α
  apply ConcreteCategory.hom_ext
  intro a
  apply CategoryTheory.Functor.functorHom_ext
  intro t β
  apply ConcreteCategory.hom_ext
  intro b
  change (F.app t ((α ≫ β) ≫ 𝟙 t) (A.map β a)).app t (𝟙 t) (B.map (𝟙 t) b) =
    (F.app e α a).app t β b
  have hn := ConcreteCategory.congr_hom (F.naturality β α) a
  have he := congrArg (fun z : ((ihom B).obj D).obj t ↦ z.app t (𝟙 t) b) hn
  change (F.app t (α ≫ β) (A.map β a)).app t (𝟙 t) b =
    (F.app e α a).app t (β ≫ 𝟙 t) b at he
  simpa only [Category.comp_id, CategoryTheory.Functor.map_id_apply] using he

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
