module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardWeightHomRows
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanConeRepresentative
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalHomogeneousComposition

/-!
# 元の Hom–Tot・正規化 BK 比較の符号つき行表示

概要：元の比較を同じ標準重み射と自由Yoneda逆評価で各行に表す。
方針：指定比較の因子分解、積成分の逆評価、元のHom–Tot成分式を合成する。
規約：IS-W2 B02の同じ成分照合の分割。比較射や符号を選び直さない。
使われ方：HA 1.2.4、全Homパラメータと実豊穣合成の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 概要：元のHomから正規化BK Homへの比較の全行の式。
方針：同じ重みの射の前合成とHom–Totの指定成分を使う。
規約：qは任意の整数。使われ方：HA 1.2.4 の実合成との符号つき成分照合。 -/
theorem homToNormalizedBousfieldKan_rows (P : Complex A)
    (X : CosimplicialObject (Complex A)) (q : ℤ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) q) (n : ℕ) :
    extendedChainHomRows normalizedBousfieldKanWeight
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) q
      ((homToNormalizedBousfieldKan P X).f q f) n =
    weightEndHomSign n q • ((normalizedBKStandardWeightMap A).f n ≫
      ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))).inv.f (q - n)
        (homTotalComponent P X q n f)) := by
  rw [homToNormalizedBousfieldKan,
    normalizedBousfieldKanHomComparison_standardWeight]
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  have hr := standardWeightHomComparison_rows normalizedBousfieldKanWeight
    (normalizedBKStandardWeightMap A) ((homDiagramFunctor P).obj X) q
    (((homTotalNatIso P).hom.app X).f q f) n
  have h := ConcreteCategory.congr_hom (homTotalNatIso_hom_component P X n q) f
  change componentπ ((homDiagramFunctor P).obj X) n q
      (((homTotalNatIso P).hom.app X).f q f) = homTotalComponent P X q n f at h
  rw [h] at hr
  exact hr

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
