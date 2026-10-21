module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedWhiskerAlgebra
public import SerrePositivity.InfinityCategories.F2.FunctorIsoWhiskerHom
/-!
概要：元の出力模型比較の射が、実導来射作用の可換四角形を満たす。
方針：型付きの交換則・元の κ・実 augmentation の三つの四角形を合成する。
規約：指定比較・計算上限を変更しない。使われ方：一般 cell 模型の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
lemma functorHom_iso_precomp_exchange {X Y Z : SSet.{w}}
    [Quasicategory Y] [Quasicategory Z]
    {f0 f1 : X ⟶ Y} {g0 g1 : Y ⟶ Z}
    (e : FunctorHom f0 f1) (d : FunctorIso g0 g1) :
    functorHomPostcomp f0 f1 g0 e ≫ (FunctorIso.precomp d f1).hom =
      (FunctorIso.precomp d f0).hom ≫ functorHomPostcomp f0 f1 g1 e := by
  simpa only [F2.functorIso_precomp_hom] using!
    functorHom_whisker_exchange_typed e d.hom
end SerrePositivity.InfinityCategories
