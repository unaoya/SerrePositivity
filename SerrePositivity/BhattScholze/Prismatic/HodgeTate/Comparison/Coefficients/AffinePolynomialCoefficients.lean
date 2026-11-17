module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons

/-!
# affine 完備多項式係数の標準変更

## 概要
prism の剰余係数の変更を、元の p 完備多項式環の間の環射へ延ばす。

## 方針
既存の主元完備化の写像と、元の完備化単位の可換式を使う。

## 規約
係数射の平坦性や、選択生成元の厳密な保存は仮定しない。

## 使われ方
元の affine 模型の係数作用と Hodge–Tate 写像の零次成分を照合する。
-/

public noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DerivedCompletion
namespace SerrePositivity.BhattScholze.Prismatic
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (r : ℕ)

/-- 元の完備化をそのまま用いる、affine 多項式係数の変更。 -/
def affinePolynomialCoefficientMap : affineAlgebra P r →+* affineAlgebra Q r :=
  principalCompletionMap (MvPolynomial.map f.quotientMap) (p : MvPolynomial (Fin r) (A ⧸ P.ideal))
    (p : MvPolynomial (Fin r) (B ⧸ Q.ideal)) (map_natCast _ p)

/-- 係数変更は、元の多項式からの完備化単位を保つ。 -/
theorem affinePolynomialCoefficientMap_unit (a : MvPolynomial (Fin r) (A ⧸ P.ideal)) :
    affinePolynomialCoefficientMap f r (prismPolynomialUnit P (Fin r) a) =
      prismPolynomialUnit Q (Fin r) (MvPolynomial.map f.quotientMap a) :=
  RingHom.congr_fun (principalCompletionMap_comp (MvPolynomial.map f.quotientMap)
    (p : MvPolynomial (Fin r) (A ⧸ P.ideal))
    (p : MvPolynomial (Fin r) (B ⧸ Q.ideal)) (map_natCast _ p)) a

/-- 完備多項式係数の変更は、同じ座標変数を保つ。 -/
theorem affinePolynomialCoefficientMap_X (j : Fin r) :
    affinePolynomialCoefficientMap f r (prismPolynomialUnit P (Fin r) (MvPolynomial.X j)) =
      prismPolynomialUnit Q (Fin r) (MvPolynomial.X j) := by
  rw [affinePolynomialCoefficientMap_unit, MvPolynomial.map_X]

/-- 元の p 完備多項式環から p 完備環への環射は、多項式上の値で決まる。 -/
theorem affinePolynomialCoefficient_ext {T : Type u} [CommRing T]
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (g h : affineAlgebra P r →+* T)
    (he : g.comp (prismPolynomialUnit P (Fin r)) = h.comp (prismPolynomialUnit P (Fin r))) :
    g = h := by
  let C := MvPolynomial (Fin r) (A ⧸ P.ideal)
  let z := h.comp (prismPolynomialUnit P (Fin r))
  letI := z.toAlgebra
  have ht : IsModuleComplete C (p : C) (ModuleCat.of C T) := by
    apply (isModuleComplete_algebraMap_iff C T (p : C) T).mp
    change IsModuleComplete T (z (p : C)) (ModuleCat.of T T)
    simpa only [map_natCast] using hT
  exact (principalCompletion_existsUnique_ringHom C (p : C) T z ht).unique he rfl

end SerrePositivity.BhattScholze.Prismatic
