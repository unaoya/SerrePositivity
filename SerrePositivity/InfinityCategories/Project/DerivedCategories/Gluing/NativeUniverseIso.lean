module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseNerveMap
public import Mathlib.CategoryTheory.Whiskering
/-!
概要：同じ単体宇宙の厳密な ULift 表示を元の全 dg nerve 作用へ戻す。
方針：型の ULift 自然同型を次数ごとに適用する。
規約：対象・全単体を保持する。使われ方：導来係数 lax 模型から元二脚への比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded

def dgGluingNativeUniverseIso (K : SSet.{v}) :
    K ≅ (SSet.uliftFunctor.{v,v}).obj K :=
  (Functor.isoWhiskerLeft K CategoryTheory.uliftFunctorTrivial ≪≫ Functor.rightUnitor _).symm

lemma dgGluingNativeUniverseNerveMap {R : Type u} [CommRing R] {C D : Type v}
    [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C D) :
    (dgGluingNativeUniverseIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap.{u,v,v,max u v} F ≫
        (dgGluingNativeUniverseIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).inv = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
