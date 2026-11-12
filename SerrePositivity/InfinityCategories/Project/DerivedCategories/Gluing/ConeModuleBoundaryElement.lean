module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeNullCochain
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitCochainElement
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction

/-! 指定した native の零ホモトピーを、Yoneda の全 Hom 写像で同じ加群境界元へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R C Y.left Z.left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f))
  (q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)))
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "W" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObjectFromRepresentatives R C D M Y Z f p q
local notation "i" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInr R C D M Y Z f p q

/-- 指定した native cochain の値を取った、同じ Hom 複体の次数 −1 元。 -/
def dgGluingConeNullElement : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M Y W).X (-1) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCochainElement _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeNullCochain R C D M Y Z f p q)

/-- 指定元の微分は、元の実合成を表す閉次数零元。 -/
lemma dgGluingConeNullElement_boundary :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M Y W).d (-1) 0
      (dgGluingConeNullElement R C D M Y Z f p q) =
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (f ≫ i))).val :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCochainElement_boundary _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeNullCochain_boundary R C D M Y Z f p q)

/-- 同じ指定元を全 Yoneda Hom で送り、全 dg 自然な加群 Hom の元にする。 -/
def dgGluingConeModuleNullElement :
    (moduleHom R G (representable R Y) (representable R W)).X (-1) :=
  (yonedaHom R G Y W).f (-1) (dgGluingConeNullElement R C D M Y Z f p q)

/-- その全加群 Hom 内の微分は、同じ二つの Yoneda 加群射の実合成。 -/
lemma dgGluingConeModuleNullElement_boundary :
    (moduleHom R G (representable R Y) (representable R W)).d (-1) 0
      (dgGluingConeModuleNullElement R C D M Y Z f p q) =
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      ((dgYoneda R G).onClosed.map f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInrModuleMap R C D M Y Z f p q))).val := by
  calc
    _ = (yonedaHom R G Y W).f 0 ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M Y W).d (-1) 0
        (dgGluingConeNullElement R C D M Y Z f p q)) := by
      exact congrArg (fun a => a (dgGluingConeNullElement R C D M Y Z f p q))
        ((yonedaHom R G Y W).comm (-1) 0)
    _ = (yonedaHom R G Y W).f 0
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (f ≫ i))).val := by
      rw [dgGluingConeNullElement_boundary]
    _ = _ := by
      change _ = (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        ((dgYoneda R G).onClosed.map f ≫ (dgYoneda R G).onClosed.map i))).val
      rw [← CategoryTheory.Functor.map_comp]
      change _ = (cycleFromUnit _
        (ForgetEnrichment.homTo (Complex R) (f ≫ i) ≫ (dgYoneda R G).map Y W)).val
      rw [cycleFromUnit_postcomp]
      rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
