module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeFunctor
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Quasicategory
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.QuasicategoryCore
/-!
概要：自由表示への全次数作用を入力関手の native dg nerve とその core へ送る。
方針：同じ実 dg 関手へ native nerve の関手性と core の関手性を適用する。
規約：ここは対象を同じ u 宇宙に置いた入口。後合成の厳密則と反復閉性は別項目。
使われ方：16時間試作の非離散な関手パラメータの高次作用を確認する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Diagnostics
open CategoryTheory DifferentialGraded _root_.SerrePositivity.KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D E : Type u)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (κ : Cardinal.{u})

def dgKappaPresentedFreeNativeFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject E κ)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeFunctor R D E κ)

lemma dgKappaPresentedFreeNativeFunctor_vertex (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) :
    (dgKappaPresentedFreeNativeFunctor R D E κ).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeAction R D E F κ) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl

def dgKappaPresentedFreeNativeCoreFunctor :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)) : SSet) ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R
        (_root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject E κ))) : SSet) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (dgKappaPresentedFreeNativeFunctor R D E κ)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Diagnostics
