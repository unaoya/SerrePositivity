module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DiscreteComplexComparison
public import SerrePositivity.HomologicalAlgebra.MapExtendComponents
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.MapComplex

/-!
概要：離散入力の複体比較の非負横次数での成分を、元の零延長同型に照合する。
方針：交代余面との交換および零延長との交換の同じ成分を展開する。
規約：新しい同型を選び直さず、discreteDoubleComplexIso の前向きの射を計算する。
使われ方：HA 1.2.4、G10 の指定成分射影と複体比較の両立。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicTopology SerrePositivity.DifferentialGraded
open scoped Simplicial SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable (A : Type u) [CommRing A]

/-- 二重複体の比較射の非負行は、二つの元の零延長同型で与えられる。 -/
theorem discreteDoubleComplexIso_hom_f
    (X : CosimplicialObject (ModuleCat.{u} A)) (n : ℕ) :
    ((discreteDoubleComplexIso A).hom.app X).f (n : ℤ) =
      (rowIso ((discreteDiagramFunctor A).obj X) n).hom ≫
        (HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).map
          ((((alternatingCofaceMapComplex (ModuleCat.{u} A)).obj X).extendXIso
            ComplexShape.embeddingUpNat (i := n) rfl).inv) := by
  let S := HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0
  let L := (alternatingCofaceMapComplex (ModuleCat.{u} A)).obj X
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

/-- 複体比較を元の余単体加群へ評価すると、同じ (n,0) 成分射影になる。 -/
theorem discreteTotalCochainNatIso_hom_f
    (X : CosimplicialObject (ModuleCat.{u} A)) (n : ℕ) :
    ((discreteTotalCochainNatIso A).hom.app X).f (n : ℤ) ≫
      (((alternatingCofaceMapComplex (ModuleCat.{u} A)).obj X).extendXIso
        ComplexShape.embeddingUpNat (i := n) rfl).hom =
    SerrePositivity.HomologicalAlgebra.ProductTotal.π
      ((doubleComplexFunctor A).obj ((discreteDiagramFunctor A).obj X)) n 0 n (by omega) ≫
      (rowIso ((discreteDiagramFunctor A).obj X) n).hom.f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (X.obj ⦋n⦌)).hom := by
  let K := ((doubleComplexFunctor A).obj ((discreteDiagramFunctor A).obj X))
  let L := (discreteCochainFunctor A).obj X
  let S := SerrePositivity.HomologicalAlgebra.ProductTotal.singleRowFunctor (ModuleCat.{u} A)
  change ((SerrePositivity.HomologicalAlgebra.ProductTotal.functor (ModuleCat.{u} A)).map
    ((discreteDoubleComplexIso A).hom.app X)).f (n : ℤ) ≫
      (SerrePositivity.HomologicalAlgebra.ProductTotal.π (S.obj L) n 0 n (by omega) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (L.X n)).hom) ≫ _ = _
  simp only [Category.assoc]
  rw [← Category.assoc]
  erw [SerrePositivity.HomologicalAlgebra.ProductTotal.map_π
    ((discreteDoubleComplexIso A).hom.app X) (n : ℤ) 0 (n : ℤ) (by omega)]
  rw [discreteDoubleComplexIso_hom_f A X n]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [HomologicalComplex.single_map_f_self]
  simp [Category.assoc]
  dsimp [L, discreteCochainFunctor]
  erw [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- 前回の次数ごとの指定同型を、内部次数零の同じ射影で書き直す。 -/
theorem discreteTotalDegreeIso_hom_zero
    (X : CosimplicialObject (ModuleCat.{u} A)) (n : ℕ) :
    (discreteTotalDegreeIso A X n).hom =
    SerrePositivity.HomologicalAlgebra.ProductTotal.π
      ((doubleComplexFunctor A).obj ((discreteDiagramFunctor A).obj X)) n 0 n (by omega) ≫
      (rowIso ((discreteDiagramFunctor A).obj X) n).hom.f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (X.obj ⦋n⦌)).hom := by
  let K := (doubleComplexFunctor A).obj ((discreteDiagramFunctor A).obj X)
  have h (b : ℤ) (hb : b = 0) :
      SerrePositivity.HomologicalAlgebra.ProductTotal.π K n b n (by omega) ≫
        (rowIso ((discreteDiagramFunctor A).obj X) n).hom.f b ≫
        (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 (X.obj ⦋n⦌) b hb).hom =
      SerrePositivity.HomologicalAlgebra.ProductTotal.π K n 0 n (by omega) ≫
        (rowIso ((discreteDiagramFunctor A).obj X) n).hom.f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (X.obj ⦋n⦌)).hom := by
    subst b
    rfl
  dsimp only [discreteTotalDegreeIso, Iso.trans_hom, singleComponentIso,
    componentπ, discreteSelfComponentIso]
  rw [Category.assoc]
  exact h ((n : ℤ) - n) (by omega)

/-- 複体比較は、前回構成した次数ごとの指定同型をそのまま保つ。 -/
theorem discreteTotalCochainNatIso_hom_f_degreeIso
    (X : CosimplicialObject (ModuleCat.{u} A)) (n : ℕ) :
    ((discreteTotalCochainNatIso A).hom.app X).f (n : ℤ) ≫
      (((alternatingCofaceMapComplex (ModuleCat.{u} A)).obj X).extendXIso
        ComplexShape.embeddingUpNat (i := n) rfl).hom =
      (discreteTotalDegreeIso A X n).hom :=
  (discreteTotalCochainNatIso_hom_f A X n).trans (discreteTotalDegreeIso_hom_zero A X n).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
