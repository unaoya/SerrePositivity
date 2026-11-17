module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TensorAdjointComparison

/-!
# 随伴で作った比較の指定行での評価

## 概要
Hom–Tot 同型の逆と随伴の単位を、元の行射影と同次テンソルで評価する。

## 方針
積への指定持ち上げと tensor–Hom 転置の既存の成分公式を使う。

## 規約
新しい比較射を選ばず、随伴で構成した鎖写像の成分を計算する。

## 使われ方
BS 著者版 Lemma 4.22 の標準比較と、符号付きの次数成分との照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex
open CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open scoped TensorProduct SerrePositivity.HomologicalAlgebra.ProductTotal

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

variable {R : Type u} [CommRing R]

/-- Hom–Tot 同型の逆は、指定行へ射影すると元の行 Hom の成分へ戻る。 -/
theorem homTotalInverse_component (P : Complex R) (K : CochainComplex (Complex R) ℤ)
    (p : ℤ) (z : ((ProductTotal.functor (ModuleCat.{u} R)).obj
      (((homFunctor P).mapHomologicalComplex (.up ℤ)).obj K)).X p)
    (i j : ℤ) (hij : i + p = j) (n t : ℤ) (hnt : n + t = j) :
    ((ProductTotal.homTotalIso P K).inv.f p z).v i j hij ≫ ProductTotal.π K n t j hnt =
      (ProductTotal.π (((homFunctor P).mapHomologicalComplex (.up ℤ)).obj K)
        n (p - n) p (by omega) z).v i t (by omega) := by
  change (ProductTotal.homTotalDegreeInverse P K p z).v i j hij ≫
    ProductTotal.π K n t j hnt = _
  change ProductTotal.lift K j _ ≫ ProductTotal.π K n t j hnt = _
  rw [ProductTotal.lift_π]

/-- 随伴の単位を同次テンソルで評価した指定公式。 -/
theorem tensorUnit_component (L Q : Complex R) (b a q : ℤ) (h : a + b = q)
    (x : Q.X b) (y : L.X a) :
    (((ihom.adjunction L).unit.app Q).f b x).v a q h y =
      (b * a).negOnePow • ιTensorObj L Q a b q h (y ⊗ₜ[R] x) := by
  have he := tensorHomEquiv_component L Q ((tensorLeft L).obj Q) (𝟙 _) b a q h x y
  change ((((ihom.adjunction L).homEquiv Q ((tensorLeft L).obj Q) (𝟙 _)).f b x).v a q h y) = _ at he
  rw [(ihom.adjunction L).homEquiv_id] at he
  rw [HomologicalComplex.id_f] at he
  have hid := ModuleCat.id_apply ((L ⊗ Q).X q)
    (ιTensorObj L Q a b q h (y ⊗ₜ[R] x))
  exact he.trans (congrArg (fun z => (b * a).negOnePow • z) hid)

/-- 全次数での転置と行での単位の二つの符号は、横次数との交換の符号になる。 -/
theorem tensorTranspose_unit_sign (a b n : ℤ) :
    (b * a).negOnePow * ((b - n) * a).negOnePow = (a * n).negOnePow := by
  rw [sub_mul, Int.negOnePow_sub, ← mul_assoc, Int.units_mul_self, one_mul, mul_comm n a]

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
