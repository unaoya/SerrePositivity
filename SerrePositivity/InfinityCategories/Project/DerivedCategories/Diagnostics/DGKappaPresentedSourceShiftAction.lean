module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceShift
public import SerrePositivity.DifferentialGraded.Functor.Closed
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor
/-!
概要：出発提示の整数 shift を全 Hom 複体の dg 自己関手と native nerve の作用にする。
方針：実加群 shift を指定した評価同型で共役し、同じラベル shift へ持ち上げる。
規約：前三角性の証明や suspension との同定は別工程。全次数成分を保持する。
使われ方：16時間試作の固定された提示模型の全高次 shift 作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Diagnostics
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (κ : Cardinal.{u})
  (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular) (D : Type u) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

def dgKappaPresentedSourceShiftFunctor (s : ℤ) :
    _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) :=
  _root_.SerrePositivity.DifferentialGraded.inducedDGFunctorClosedConjugate R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ)
    (moduleShiftDG R D s) (fun X => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceShift R κ hκ hreg D X s)
    (fun X => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceShiftIso R κ hκ hreg D X s).symm)

lemma dgKappaPresentedSourceShiftFunctor_obj (s : ℤ) (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) :
    (dgKappaPresentedSourceShiftFunctor R κ hκ hreg D s).obj X =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceShift R κ hκ hreg D X s := rfl

def dgKappaPresentedSourceNativeShift (s : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaPresentedSourceShiftFunctor R κ hκ hreg D s)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Diagnostics
