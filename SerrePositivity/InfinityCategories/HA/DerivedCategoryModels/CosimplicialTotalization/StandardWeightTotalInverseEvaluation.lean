module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKStandardWeight
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ProductComponents

/-!
# 指定標準重み比較の逆射の積成分評価

概要：元の積Totから標準重みendへ戻る逆射を、同じ自由Yonedaの逆射で評価する。
方針：既存の前向き成分式と積射影の自然性を使う。
規約：IS-W2 B02の同じ成分照合の分割。対象も射も選び直さない。
使われ方：HA 1.2.4、元のBK Hom比較の符号つき各行の計算。
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

/-- 概要：標準重み比較の逆射の各行は同じ自由単位評価の逆射。
方針：既存の前向き成分式で同型を同定する。
規約：元の行同型を保持。使われ方：HA 1.2.4 の指定逆射の評価。 -/
theorem standardWeightEndCochainIso_inv_f (X : CosimplicialObject (Complex A)) (n : ℕ) :
    (standardWeightEndCochainIso X).inv.f n =
      ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app (doubleOppositeDiagram X)).inv := by
  let e := (HomologicalComplex.eval (Complex A) (.up ℕ) n).mapIso
    (standardWeightEndCochainIso X)
  have he : e = (freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app
      (doubleOppositeDiagram X) := by
    apply Iso.ext
    exact standardWeightEndCochainIso_hom_f X n
  exact congrArg Iso.inv he

/-- 概要：指定積射影は標準重みへの逆比較を各行の逆評価へ送る。
方針：積全複体の成分自然性と逆射の行の式。
規約：内部次数qは任意整数。使われ方：HA 1.2.4 の非有界Hom成分の照合。 -/
theorem standardWeightEndTotalIso_inv_component
    (X : CosimplicialObject (Complex A)) (n : ℕ) (q : ℤ) :
    (standardWeightEndTotalIso X).inv.f q ≫
      CochainProductTotal.componentπ
        ((linearWeightEndCochainFunctor A (doubleOppositeDiagram X)).obj
          (Opposite.op ((alternatingFaceMapComplex _).obj
            (standardSimplexWeight (ModuleCat.of A A))))) n q =
    componentπ X n q ≫
      ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app
        (doubleOppositeDiagram X)).inv.f (q - n) := by
  have h := CochainProductTotal.componentπ_naturality (standardWeightEndCochainIso X).inv n q
  rw [standardWeightEndCochainIso_inv_f] at h
  exact h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
