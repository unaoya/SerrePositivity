module

public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceTargetComparison
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantAlgebraRelativeInput
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrowElements

/-!
# 元の source frame を同じ cofibrant DK 入力へ持ち上げる

概要：既存の関手的 Reedy 解像の全対象・全射・augmentation を保持する。
方針：各次数の cofibrancy で元の全部分圏へ持ち上げ、Hom の宇宙だけを揃える。
規約：任意可換環。新しい置換・frame・指定弱同値を選ばない。
使われ方：既存 sourceFrameHom と実 hammock の右 Kan 計算の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory _root_.HomotopicalAlgebra SerrePositivity.Reedy
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
variable (A : Type u) [CommRing A] (X : CofibrantAlgebra A)

def cofibrantSourceFrame : SimplexCategory ⥤ CofibrantAlgebra A := by
  let := modelCategory A
  let q := (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).atObject X.obj
  exact (cofibrantObjects (operad A).Algebra).lift q.obj q.isCofibrant_obj

lemma cofibrantSourceFrame_inclusion :
    cofibrantSourceFrame A X ⋙ cofibrantAlgebraInclusion A =
      let := modelCategory A
      (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).obj.obj X.obj := rfl

def cofibrantSourceFrameAugmentation :
    cofibrantSourceFrame A X ⟶ (Functor.const SimplexCategory).obj X := by
  let := modelCategory A
  let q := (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).atObject X.obj
  exact
    { app n := ObjectProperty.homMk (q.augmentation.app n)
      naturality _ _ f := by
        apply ObjectProperty.hom_ext
        exact q.augmentation.naturality f }

lemma cofibrantSourceFrameAugmentation_weak (n : SimplexCategory) :
    cofibrantAlgebraWeakEquivalences A ((cofibrantSourceFrameAugmentation A X).app n) := by
  let := modelCategory A
  let q := (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).atObject X.obj
  exact q.augmentation_weakEquivalence n

lemma cofibrantSourceFrame_map_weak {n m : SimplexCategory} (f : n ⟶ m) :
    cofibrantAlgebraWeakEquivalences A ((cofibrantSourceFrame A X).map f) := by
  let := modelCategory A
  let q := (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).atObject X.obj
  exact q.homotopicallyConstant f

def cofibrantDKSourceFrame : AsSmall.{u + 1} SimplexCategory ⥤
    (cofibrantAlgebraRelativeCategory A).category :=
  AsSmall.down.{0, 0, u + 1} ⋙ cofibrantSourceFrame A X ⋙
    ULiftHom.up.{u, u + 1, u + 1}

lemma cofibrantDKSourceFrame_map_weak {n m : AsSmall.{u + 1} SimplexCategory} (f : n ⟶ m) :
    (cofibrantAlgebraRelativeCategory A).weakEquivalences ((cofibrantDKSourceFrame A X).map f) :=
  cofibrantSourceFrame_map_weak A X (AsSmall.down.map f)

end SerrePositivity.EInfinity.BarrattEccles
