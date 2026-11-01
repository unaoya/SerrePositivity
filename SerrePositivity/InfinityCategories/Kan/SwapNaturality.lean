module
public import SerrePositivity.InfinityCategories.Kan.SwapEvaluation

/-! # 二重内部 Hom の交換の自然性
概要：内部 Hom の交換は標的への後合成と最初の添字への制限に関して厳密に自然。
方針：全パラメーターの成分計算と既存の第二添字の自然性・二回交換の逆律を使う。
規約：頂点評価だけへ弱めない。使われ方：二重 S 構成の自然な交換同型。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories

/-- 二重内部 Hom の交換は標的の後合成について全単体で厳密に自然。 -/
lemma internalHomSwap_postcomp {A B C D : SSet.{u}} (f : C ⟶ D) :
    (ihom A).map ((ihom B).map f) ≫ (internalHomSwapIso A B D).hom =
      (internalHomSwapIso A B C).hom ≫ (ihom B).map ((ihom A).map f) := by
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
  rfl

/-- 二重内部 Hom の交換は最初の添字の前合成について全単体で厳密に自然。 -/
lemma internalHomSwap_pre_left {A A' B C : SSet.{u}} (i : A' ⟶ A) :
    (pre i).app ((ihom B).obj C) ≫ (internalHomSwapIso A' B C).hom =
      (internalHomSwapIso A B C).hom ≫ (ihom B).map ((pre i).app C) := by
  apply (cancel_mono (internalHomSwapIso B A' C).hom).mp
  calc
    _ = (pre i).app ((ihom B).obj C) := by
      rw [Category.assoc, internalHomSwap_twice, Category.comp_id]
    _ = (internalHomSwapIso A B C).hom ≫
        ((internalHomSwapIso B A C).hom ≫ (pre i).app ((ihom B).obj C)) := by
      rw [← Category.assoc, internalHomSwap_twice, Category.id_comp]
    _ = _ := by
      rw [← internalHomSwapIso_pre, ← Category.assoc]

end SerrePositivity.KST.SConstruction
