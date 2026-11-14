module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalZeroRow
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomToNormalizedBKRows
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKConeComposition

/-!
概要：元の正規化BK錐代表の第0行は、同じ標準零行射影の自由単位重み評価。
方針：元のHom–Totの全行の式を恒等射・第0行に特殊化する。
規約：IS-W2 C01の既存構成の単位・評価則。錐代表を選び直さない。
使われ方：HA 1.2.4、指定native脚の最終閉零射の計算。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory HomologicalComplex CochainComplex HomComplex AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 元のBK錐代表の第0行は、同じ標準射影の自由単位重みへの逆評価。 -/
theorem normalizedBousfieldKanConeRepresentative_zero_row
    (X : CosimplicialObject (Complex A)) :
    let T := (productTotalFunctor A).obj X
    let H := doubleOppositeDiagram ((homDiagramFunctor T).obj X)
    (negativeChainRowIso (normalizedBousfieldKanWeight (A := A)) 0).inv ≫
      (normalizedBousfieldKanConeRepresentative X).f 0 =
    (normalizedBKStandardWeightMap A).f 0 ≫
      ((freeUnitWeightEndNatIso A (Opposite.op ⦋0⦌)).inv.app H).f 0
        (Cochain.ofHom (standardZeroLeg A X)) := by
  let T := (productTotalFunctor A).obj X
  have h := homToNormalizedBousfieldKan_rows T X 0 (Cochain.ofHom (𝟙 T)) 0
  erw [homTotalComponent_zero_ofHom] at h
  rw [Category.id_comp] at h
  rw [← normalizedBousfieldKanRepresentative_cochain T X (𝟙 T)] at h
  change (negativeChainRowIso (normalizedBousfieldKanWeight (A := A)) 0).inv ≫
      (normalizedBousfieldKanConeRepresentative X).f 0 = _ at h
  have hs : weightEndHomSign 0 (0 : ℤ) = 1 := by
    norm_num [weightEndHomSign, alternatingFaceReverseSign]
  rw [hs, one_smul] at h
  exact h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
