module
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedFreeFunctor
public import SerrePositivity.InfinityCategories.DGNerve.Functor
public import SerrePositivity.InfinityCategories.DGNerve.Quasicategory
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryCore
/-!
概要：自由表示への全次数作用を入力関手の native dg nerve とその core へ送る。
方針：同じ実 dg 関手へ native nerve の関手性と core の関手性を適用する。
規約：ここは対象を同じ u 宇宙に置いた入口。後合成の厳密則と反復閉性は別項目。
使われ方：16時間試作の非離散な関手パラメータの高次作用を確認する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SerrePositivity.KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R] (D E : Type u)
  [DGCategory R D] [DGCategory R E] (κ : Cardinal.{u})

def dgKappaPresentedFreeNativeFunctor :
    dgNerve R (DGFunctor R D E) ⟶
      dgNerve R (DGFunctor R (DGKappaPresentedFreeObject D κ) (DGKappaPresentedFreeObject E κ)) :=
  dgNerve.map (dgKappaPresentedFreeFunctor R D E κ)

lemma dgKappaPresentedFreeNativeFunctor_vertex (F : DGFunctor R D E) :
    (dgKappaPresentedFreeNativeFunctor R D E κ).app (Opposite.op ⦋0⦌) (Simplex.vertex F) =
      Simplex.vertex (dgKappaPresentedFreeAction R D E F κ) := by
  apply Simplex.vertexEquiv.injective
  rfl

def dgKappaPresentedFreeNativeCoreFunctor :
    (quasicategoryCore (dgNerve R (DGFunctor R D E)) : SSet) ⟶
      (quasicategoryCore (dgNerve R
        (DGFunctor R (DGKappaPresentedFreeObject D κ) (DGKappaPresentedFreeObject E κ))) : SSet) :=
  quasicategoryCoreMap (dgKappaPresentedFreeNativeFunctor R D E κ)

end SerrePositivity.InfinityCategories
