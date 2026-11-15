module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ElementsUnderProjectionIso
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanWeightPost
public import Mathlib.CategoryTheory.Category.Cat.Op

/-!
概要：要素圏の射影に沿う指定BK重みの比較射は同型。
方針：固定始点の厳密な同型を反対圏のOver表示へ移し、nerveを取る。
使われ方：HTT 4.2.4.4、RR02(a)の要素圏実現の制限重みの同定。
規約：順方向の射は既存のbousfieldKanWeightPostそのもの。
-/

@[expose] public noncomputable section
universe w
open CategoryTheory
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.ElementsUnderProjection

/-- Overの反対圏表示は、指定した厳密な圏同型を与える。 -/
def overOpUnderIso {K : Type w} [SmallCategory K] (e : K) :
    Cat.of (Over (Opposite.op e)) ≅ Cat.of ((Under e)ᵒᵖ) :=
  Cat.isoOfEquiv (Over.opEquivOpUnder e) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl)

variable {K : Type w} [SmallCategory K] (F : K ⥤ Type w) (e : F.Elements)

/-- 指定要素射影によるOver圏のnerveの同型。 -/
def overNerveIso : nerve (Over (Opposite.op e)) ≅ nerve (Over (Opposite.op e.obj)) :=
  nerveFunctor.mapIso (overOpUnderIso e ≪≫
    Cat.opFunctor.mapIso (catIso F e) ≪≫ (overOpUnderIso e.obj).symm)

lemma overNerveIso_hom : (overNerveIso F e).hom =
    nerveMap (Over.post (Functor.Elements.π F).op (X := Opposite.op e)) := rfl

/-- 全要素の厳密な比較を、同じBK重みの自然同型に束ねる。 -/
def weightIso : bousfieldKanWeight F.Elementsᵒᵖ ≅
    (Functor.Elements.π F).op ⋙ bousfieldKanWeight Kᵒᵖ := by
  letI (e : F.Elementsᵒᵖ) : IsIso
      ((bousfieldKanWeightPost (Functor.Elements.π F).op).app e) := by
    change IsIso (nerveMap (Over.post (Functor.Elements.π F).op (X := e)))
    rw [← overNerveIso_hom F e.unop]
    infer_instance
  letI := NatIso.isIso_of_isIso_app (bousfieldKanWeightPost (Functor.Elements.π F).op)
  exact asIso (bousfieldKanWeightPost (Functor.Elements.π F).op)

lemma weightIso_hom : (weightIso F).hom =
    bousfieldKanWeightPost (Functor.Elements.π F).op := rfl

end SerrePositivity.DiagramModel.ElementsUnderProjection
