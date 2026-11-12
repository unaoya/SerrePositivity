module

public import SerrePositivity.EInfinity.PowerOperation.ComplexRelativeElementColumn

/-!
# 元の全複体と相対表示の nerve の同じ往復

DAG XIII §2.2 の native なスペクトル忘却の通常始域比較の補助。
異なる Hom 宇宙の全射列を直接写す。［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

def complexRelativeNerveUp : nerve (Complex A) ⟶ nerve (complexRelativeCategory A).category where
  app _ := ↾fun Γ => ((complexRelativeUp A).mapComposableArrows _).obj Γ

lemma complexRelativeNerveUp_down :
    complexRelativeNerveUp A ≫ complexRelativeNerveDown A = 𝟙 (nerve (Complex A)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Γ
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end SerrePositivity.EInfinity.PowerOperation
