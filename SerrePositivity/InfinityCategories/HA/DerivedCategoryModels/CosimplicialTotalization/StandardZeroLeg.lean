module
public import SerrePositivity.HomologicalAlgebra.ProductTotalZeroRow
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ProductComponents

/-!
概要：余単体的積全複体から元の余単体次数零への標準脚を自然変換として固定する。
方針：負の行が零であることを使って零行の射影を鎖写像にし、零延長の指定同型と合成する。
規約：対象ごとの選択を行わず、同じ全関手の射と標準脚を保持する。
使われ方：HA 1.2.4、HTT 4.2.4.1。G10 の native 錐との比較の零次の入口。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicTopology SerrePositivity.DifferentialGraded
open scoped Simplicial SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable (A : Type u) [CommRing A]

/-- 零行へ入る横微分は、負の行が零なので消える。 -/
theorem negativeToZeroRow_d (X : CosimplicialObject (Complex A)) :
    ((doubleComplexFunctor A).obj X).d (-1) 0 = 0 :=
  (negativeRow_isZero X (-1) (by omega)).eq_of_src _ _

/-- 元の余単体次数零へ向かう指定標準脚。 -/
def standardZeroLeg (X : CosimplicialObject (Complex A)) :
    (productTotalFunctor A).obj X ⟶ X.obj ⦋0⦌ :=
  SerrePositivity.HomologicalAlgebra.ProductTotal.zeroRowHom
    ((doubleComplexFunctor A).obj X) (negativeToZeroRow_d A X) ≫ (rowIso X 0).hom

/-- 同じ標準脚は、元の余単体的複体の射と厳密に可換。 -/
theorem standardZeroLeg_naturality {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    (productTotalFunctor A).map f ≫ standardZeroLeg A Y =
      standardZeroLeg A X ≫ f.app ⦋0⦌ := by
  dsimp only [standardZeroLeg, productTotalFunctor, Functor.comp_map]
  rw [← Category.assoc, SerrePositivity.HomologicalAlgebra.ProductTotal.zeroRowHom_naturality
    ((doubleComplexFunctor A).map f) (negativeToZeroRow_d A X) (negativeToZeroRow_d A Y),
    Category.assoc]
  erw [rowIso_naturality f 0]
  rw [← Category.assoc]

/-- 積全複体から次数零の評価への自然変換。 -/
def standardZeroLegNatTrans :
    productTotalFunctor A ⟶ (evaluation SimplexCategory (Complex A)).obj ⦋0⦌ where
  app := standardZeroLeg A
  naturality _ _ f := standardZeroLeg_naturality A f

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
