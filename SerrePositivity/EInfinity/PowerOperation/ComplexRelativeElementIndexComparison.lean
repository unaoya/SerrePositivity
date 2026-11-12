module

public import SerrePositivity.EInfinity.PowerOperation.ComplexRelativeElementColumn
public import SerrePositivity.EInfinity.PowerOperation.ComplexNormalizedRoofWeak

/-!
# 同じ正規化全要素圏の相対表示と frame 表示の実同型

DAG XIII §2.2 の native な降下の補助。全単体・全作用素を変更せず、
ULift の入れ子だけを取り除く。［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory Opposite
attribute [local instance] uliftCategory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
variable (A : Type u) [CommRing A] (X Y : Complex A)

abbrev complexNormalizedRawIndex :=
  ULiftHom.{u + 1} (((((normalizedProbeTensorHom A).obj (op X)).obj Y).Elements)ᵒᵖ)

def complexRelativeElementIndexDown :
    complexRelativeElementIndex A ((framedLimitProbeFunctor A).obj X) Y ⥤
      complexNormalizedRawIndex A X Y :=
  ULiftHom.down.{u, u + 1, u + 1} ⋙ ULiftHom.down.{0, u + 1, u} ⋙
    ULift.downFunctor ⋙ ULiftHom.up.{0, u, u + 1}

def complexRelativeElementIndexUp :
    complexNormalizedRawIndex A X Y ⥤
      complexRelativeElementIndex A ((framedLimitProbeFunctor A).obj X) Y :=
  ULiftHom.down.{0, u, u + 1} ⋙ ULift.upFunctor ⋙ ULiftHom.up.{0, u + 1, u} ⋙
    ULiftHom.up.{u, u + 1, u + 1}

def complexRelativeElementIndexDownNerve :
    nerve (complexRelativeElementIndex A ((framedLimitProbeFunctor A).obj X) Y) ⟶
      nerve (complexNormalizedRawIndex A X Y) where
  app _ := ↾fun Γ => Γ ⋙ complexRelativeElementIndexDown A X Y
  naturality _ _ _ := rfl

def complexRelativeElementIndexUpNerve :
    nerve (complexNormalizedRawIndex A X Y) ⟶
      nerve (complexRelativeElementIndex A ((framedLimitProbeFunctor A).obj X) Y) where
  app _ := ↾fun Γ => Γ ⋙ complexRelativeElementIndexUp A X Y
  naturality _ _ _ := rfl

/-- 同じ元の全要素の nerve の表示変更そのものが実同型である。 -/
def complexRelativeElementIndexIso :
    nerve (complexRelativeElementIndex A ((framedLimitProbeFunctor A).obj X) Y) ≅
      nerve (complexNormalizedRawIndex A X Y) where
  hom := complexRelativeElementIndexDownNerve A X Y
  inv := complexRelativeElementIndexUpNerve A X Y
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro Γ
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro Γ
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

end SerrePositivity.EInfinity.PowerOperation
