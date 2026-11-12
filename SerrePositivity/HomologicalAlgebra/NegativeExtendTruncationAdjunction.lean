module
public import SerrePositivity.HomologicalAlgebra.NegativeExtendTruncationTarget
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
概要：負次数への零延長と実 smart 切断を、元の Hom 同値による随伴としてまとめる。
方針：構成済みの両自然性を随伴の Hom 同値の公理へ渡す。
規約：逆写像は指定延長射と切断包含の合成のまま。
使われ方：HA 1.2.4、G10 の点ごとの切断と図式圏の切断の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable (C : Type u) [Category.{v} C] [Abelian C]

/-- 指定 Hom 同値で定めた、負次数延長と零での smart 切断の随伴。 -/
def negativeExtendTruncationAdjunction :
    ComplexShape.embeddingDownNat.extendFunctor C ⊣
      (ComplexShape.embeddingUpIntLE 0).truncLE'Functor C :=
  Adjunction.mkOfHomEquiv {
    homEquiv := negativeExtendTruncationHomEquiv
    homEquiv_naturality_left_symm := by
      intro K L H f g
      apply (negativeExtendTruncationHomEquiv K H).injective
      erw [Equiv.apply_symm_apply, negativeExtendTruncationHomEquiv_precomp,
        Equiv.apply_symm_apply]
    homEquiv_naturality_right := by
      intro K H H' f g
      exact negativeExtendTruncationHomEquiv_postcomp K f g }

end SerrePositivity.HomologicalAlgebra
