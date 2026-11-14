module
public import SerrePositivity.HomologicalAlgebra.NegativeExtendTruncationTarget
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence

/-!
概要：アーベル圏値の実正規化重みからの複体射を、元の単体的重みからの Dold–Kan 射へ移す。
方針：負次数延長・smart 切断の Hom 同値と Dold–Kan 随伴の Hom 同値を合成する。
規約：図式圏での正規化にも適用し、元の単体的重みの全射への自然性を保つ。
使われ方：HA 1.2.4、G10 の BK 重みと Hom 空間の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits HomologicalComplex CochainComplex AlgebraicTopology
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- 実 Moore 正規化の負次数延長からの射と、元の単体的重みからの射の同値。 -/
def normalizedWeightHomEquiv (W : SimplicialObject C) (H : CochainComplex C ℤ) :
    (((normalizedMooreComplex C).obj W).extend ComplexShape.embeddingDownNat ⟶ H) ≃
      (W ⟶ (Abelian.DoldKan.Γ : ChainComplex C ℕ ⥤ SimplicialObject C).obj
        (H.truncLE' (ComplexShape.embeddingUpIntLE 0))) :=
  (negativeExtendTruncationHomEquiv ((normalizedMooreComplex C).obj W) H).trans
    ((Abelian.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ).toAdjunction.homEquiv _ _)

/-- 正規化 Hom 同値は元の単体的重みの全射による前合成と可換。 -/
theorem normalizedWeightHomEquiv_precomp {V W : SimplicialObject C}
    (g : V ⟶ W) (H : CochainComplex C ℤ)
    (f : ((normalizedMooreComplex C).obj W).extend ComplexShape.embeddingDownNat ⟶ H) :
    normalizedWeightHomEquiv V H
        (extendMap ((normalizedMooreComplex C).map g) ComplexShape.embeddingDownNat ≫ f) =
      g ≫ normalizedWeightHomEquiv W H f := by
  change (Abelian.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ).toAdjunction.homEquiv _ _
    (negativeExtendTruncationHomEquiv _ H _) = _
  rw [negativeExtendTruncationHomEquiv_precomp]
  exact (Abelian.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ).toAdjunction.homEquiv_naturality_left _ _

/-- 正規化 Hom 同値は元の標的複体の全射による後合成と可換。 -/
theorem normalizedWeightHomEquiv_postcomp (W : SimplicialObject C)
    {H H' : CochainComplex C ℤ}
    (f : ((normalizedMooreComplex C).obj W).extend ComplexShape.embeddingDownNat ⟶ H)
    (g : H ⟶ H') :
    normalizedWeightHomEquiv W H' (f ≫ g) =
      normalizedWeightHomEquiv W H f ≫
        (Abelian.DoldKan.Γ : ChainComplex C ℕ ⥤ SimplicialObject C).map
          (truncLE'Map g (ComplexShape.embeddingUpIntLE 0)) := by
  change (Abelian.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ).toAdjunction.homEquiv _ _
    (negativeExtendTruncationHomEquiv _ H' _) = _
  rw [negativeExtendTruncationHomEquiv_postcomp]
  exact (Abelian.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ).toAdjunction.homEquiv_naturality_right _ _

end SerrePositivity.HomologicalAlgebra
