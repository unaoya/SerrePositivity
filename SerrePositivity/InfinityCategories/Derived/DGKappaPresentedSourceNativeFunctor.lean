module
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedSourceFunctor
public import SerrePositivity.InfinityCategories.DGNerve.Functor
public import SerrePositivity.InfinityCategories.DGNerve.Quasicategory
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryCore
/-!
概要：出発提示表示への全次数作用を入力関手の native dg nerve とその core へ送る。
方針：同じ実 dg 関手へ native nerve の関手性と core の関手性を適用する。
規約：ここは対象を同じ u 宇宙に置いた入口。後合成の厳密則は既証明、表示の反復閉性は別項目。
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

def dgKappaPresentedSourceNativeFunctor :
    dgNerve R (DGFunctor R D E) ⟶
      dgNerve R (DGFunctor R (DGKappaPresentedSourceObject R D κ)
        (DGKappaPresentedSourceObject R E κ)) :=
  dgNerve.map (dgKappaPresentedSourceFunctor R D E κ)

lemma dgKappaPresentedSourceNativeFunctor_vertex (F : DGFunctor R D E) :
    (dgKappaPresentedSourceNativeFunctor R D E κ).app (Opposite.op ⦋0⦌) (Simplex.vertex F) =
      Simplex.vertex (dgKappaPresentedSourceAction R D E κ F) := by
  apply Simplex.vertexEquiv.injective
  rfl

def dgKappaPresentedSourceNativeCoreFunctor :
    (quasicategoryCore (dgNerve R (DGFunctor R D E)) : SSet) ⟶
      (quasicategoryCore (dgNerve R
        (DGFunctor R (DGKappaPresentedSourceObject R D κ)
          (DGKappaPresentedSourceObject R E κ))) : SSet) :=
  quasicategoryCoreMap (dgKappaPresentedSourceNativeFunctor R D E κ)

end SerrePositivity.InfinityCategories
