module
public import SerrePositivity.HomologicalAlgebra.ComplexHomAdditive
public import SerrePositivity.HomologicalAlgebra.MapExtendComponents
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.MapComplex
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.MapComplex
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ProductComponents

/-!
概要：各余単体成分に Hom を適用した二重複体と、元の二重複体の各行への Hom の自然同型。
方針：既存の加法的関手と交代余面の交換、零延長との交換を合成する。
規約：入力図式の射を含む全関手の比較。Hom と積 Tot 自体の交換は別に証明する。
使われ方：HA 1.2.4、G10 の Hom–Tot 比較の標的を元の行の Hom に戻す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicTopology SerrePositivity.DifferentialGraded
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 各余単体成分への Hom を取る全関手。 -/
def homDiagramFunctor (P : Complex A) :
    CosimplicialObject (Complex A) ⥤ CosimplicialObject (Complex A) :=
  (CosimplicialObject.whiskering (Complex A) (Complex A)).obj (homFunctor P)

/-- Hom を図式に適用する操作と交代余面・零延長の交換。 -/
def homDoubleComplexIso (P : Complex A) :
    homDiagramFunctor P ⋙ doubleComplexFunctor A ≅
      doubleComplexFunctor A ⋙ (homFunctor P).mapHomologicalComplex (.up ℤ) := by
  let h₁ := Functor.isoWhiskerRight
    (SerrePositivity.Cosimplicial.alternatingCofaceMapComplexCompMapHomologicalComplexIso
      (homFunctor P)).symm
    (ComplexShape.embeddingUpNat.extendFunctor (Complex A))
  let h₂ := Functor.isoWhiskerLeft (alternatingCofaceMapComplex (Complex A))
    (SerrePositivity.HomologicalAlgebra.mapExtendNatIso (homFunctor P)
      ComplexShape.embeddingUpNat).symm
  exact h₁ ≪≫ h₂

/-- 前向き比較は、元の指定行同型とその Hom 像で与えられる。 -/
theorem homDoubleComplexIso_hom_f (P : Complex A)
    (X : CosimplicialObject (Complex A)) (n : ℕ) :
    ((homDoubleComplexIso P).hom.app X).f (n : ℤ) =
      (rowIso ((homDiagramFunctor P).obj X) n).hom ≫
        (homFunctor P).map (rowIso X n).inv := by
  let S := homFunctor P
  let L := (alternatingCofaceMapComplex (Complex A)).obj X
  let α := SerrePositivity.Cosimplicial.alternatingCofaceMapComplexCompMapHomologicalComplexIso S
  change (HomologicalComplex.extendMap (α.inv.app X) ComplexShape.embeddingUpNat).f (n : ℤ) ≫
    (SerrePositivity.HomologicalAlgebra.mapExtendIso S ComplexShape.embeddingUpNat L).inv.f (n : ℤ) = _
  rw [HomologicalComplex.extendMap_f (α.inv.app X) ComplexShape.embeddingUpNat
    (i := n) (i' := (n : ℤ)) rfl,
    SerrePositivity.HomologicalAlgebra.mapExtendIso_inv_f S ComplexShape.embeddingUpNat L
      (i := n) (j := (n : ℤ)) rfl]
  simp [α, SerrePositivity.Cosimplicial.alternatingCofaceMapComplexCompMapHomologicalComplexIso,
    Category.assoc, rowIso]
  erw [Category.id_comp]
  rfl

/-- 上記の行の比較を同じ積全複体関手に通した自然同型。 -/
def homDiagramTotalIso (P : Complex A) :
    homDiagramFunctor P ⋙ productTotalFunctor A ≅
      (doubleComplexFunctor A ⋙ (homFunctor P).mapHomologicalComplex (.up ℤ)) ⋙
        SerrePositivity.HomologicalAlgebra.ProductTotal.functor (ModuleCat.{u} A) :=
  Functor.isoWhiskerRight (homDoubleComplexIso P)
    (SerrePositivity.HomologicalAlgebra.ProductTotal.functor (ModuleCat.{u} A))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
