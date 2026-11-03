module
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedSourceShift
public import SerrePositivity.DifferentialGraded.Functor.Closed
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.InfinityCategories.DGNerve.Functor
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (κ : Cardinal.{u})
  (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular) (D : Type u) [DGCategory R D]

def dgKappaPresentedSourceShiftFunctor (s : ℤ) :
    DGFunctor R (DGKappaPresentedSourceObject R D κ) (DGKappaPresentedSourceObject R D κ) :=
  inducedDGFunctorClosedConjugate R
    (dgKappaPresentedSourceValue R D κ) (dgKappaPresentedSourceValue R D κ)
    (moduleShiftDG R D s) (fun X => dgKappaPresentedSourceShift R κ hκ hreg D X s)
    (fun X => (dgKappaPresentedSourceShiftIso R κ hκ hreg D X s).symm)

lemma dgKappaPresentedSourceShiftFunctor_obj (s : ℤ) (X : DGKappaPresentedSourceObject R D κ) :
    (dgKappaPresentedSourceShiftFunctor R κ hκ hreg D s).obj X =
      dgKappaPresentedSourceShift R κ hκ hreg D X s := rfl

def dgKappaPresentedSourceNativeShift (s : ℤ) :
    dgNerve R (DGKappaPresentedSourceObject R D κ) ⟶
      dgNerve R (DGKappaPresentedSourceObject R D κ) :=
  dgNerve.map (dgKappaPresentedSourceShiftFunctor R κ hκ hreg D s)

end SerrePositivity.InfinityCategories
