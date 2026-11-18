module

public import SerrePositivity.InfinityCategories.Sheaves.RelativeCechPointComma
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
概要：集合値前層の各点での全射から、同じ相対 Čech 余錐の表現可能 Hom 値の余極限性を得る。
方針：既存の Yoneda の全単射で各射を持ち上げ、構成済みの同じ Čech 判定を適用する。
規約：HTT 6.2.2.6 の Čech 解消への入力。局所全射から各点全射を仮定しない。
使われ方：S8 で像への全射の Čech 解消を使う。像の包含は別に局所単射性で扱う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u}

/-- 各点での全射は、任意の元の表現可能からの射を同じ Yoneda 対応で持ち上げる。 -/
lemma presheafSurjective_yoneda_lift (f : P ⟶ Q)
    (hf : ∀ X : Cᵒᵖ, Function.Surjective (f.app X)) (U : C)
    (r : yoneda.obj U ⟶ Q) : ∃ a : yoneda.obj U ⟶ P, a ≫ f = r := by
  obtain ⟨p, hp⟩ := hf (Opposite.op U) (yonedaEquiv r)
  refine ⟨yonedaEquiv.symm p, ?_⟩
  apply yonedaEquiv.injective
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using hp

/-- 元の商への全射の同じ相対 Čech 余錐は、各表現可能 Hom 値で空間の余極限。 -/
lemma presheafRelativeCechHomCocone_isColimit (f : P ⟶ Q)
    (hf : ∀ X : Cᵒᵖ, Function.Surjective (f.app X)) (U : C) :
    IsColimitCone
      (strictNativeCocone (setsToKan.mapCocone (relativeCechHomCocone f (yoneda.obj U)))) :=
  relativeCechHomCocone_isColimit f (presheafSurjective_yoneda_lift f hf U)

end SerrePositivity.InfinityCategories.Sheaves
