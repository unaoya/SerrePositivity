module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.ConstantEdgeFamily

/-!
概要：定値関手間の射の像の可逆性を、元の射の像から導く。
方針：後合成の自然性と同型による共役を使う。
規約：全パラメータと任意の標的を扱う。使われ方：実分母の関手圏内での反転。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 元の射の像が可逆なら、その定値パラメータ族の後合成像も可逆。 -/
lemma constantFunctorHomMap_image_isIso {K X Y : SSet.{u}} (F : X ⟶ Y)
    {x y : X _⦋0⦌} (f : (SSet.HomotopyCategory.mk x : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk y)
    [IsIso ((hoFunctor.map F).toFunctor.map f)] :
    IsIso ((hoFunctor.map ((ihom K).map F)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K f)) := by
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso K x F
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso K y F
  let g := (hoFunctor.map ((ihom K).map F)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K f)
  have hc : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K ((hoFunctor.map F).toFunctor.map f)) := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap]
    infer_instance
  have h : i.inv ≫ g ≫ j.hom = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K ((hoFunctor.map F).toFunctor.map f) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_postcomp K F f
  have h' : IsIso (i.inv ≫ g ≫ j.hom) := h.symm ▸ hc
  have h'' : IsIso (g ≫ j.hom) := (isIso_comp_left_iff i.inv (g ≫ j.hom)).mp h'
  exact (isIso_comp_right_iff g j.hom).mp h''
end SerrePositivity.InfinityCategories.Project.DerivedCategories
