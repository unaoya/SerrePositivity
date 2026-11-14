module

public import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RepeatedPrincipalRing
import all SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensor
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.RepeatedPrincipalRing
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 結晶的な基底の完備テンソル

## 概要
生成元が p の prism 上では、二座標完備テンソルを通常テンソルの p 完備化に同定する。

## 方針
左脚が自然数 p を保つことから、二座標を (p,p) に書き直す。

## 規約
左係数・右係数の脚を保つ。完備環の比較に平坦性を仮定しない。

## 使われ方
BS 著者版 Theorem 6.4、有限 affine 模型の Witt 係数変更を項ごとに同定する。
-/

public noncomputable section
open CategoryTheory
open scoped TensorProduct
open SerrePositivity.DerivedCompletion
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
variable (Q : OrientedPrism p B) (hQ : Q.generator = (p : B))

private def coordinateEquiv (R : Type u) [CommRing R] (d : R) (hd : d = (p : R)) :
    letI := pdCompletionCommRing R p d
    PDCompletionH0 R p d ≃+* CompletedRing p R := by
  subst d
  exact repeatedPrincipalRingEquiv p R

omit [Fact p.Prime] in
private theorem coordinateEquiv_unit (R : Type u) [CommRing R] (d : R)
    (hd : d = (p : R)) (x : R) :
    coordinateEquiv R d hd (pdCompletionUnit R p d x) =
      principalCompletionRingCatUnit p (CommRingCat.of R) x := by
  subst d
  exact repeatedPrincipalRingEquiv_unit p R x

/-- 結晶的な生成元の完備テンソルを、一座標の主完備環に同定する。 -/
def crystallineCompletedTensorRingEquiv :
    PrismCompletedTensor (A := A) (C := C) Q ≃+* CompletedRing p (B ⊗[A] C) :=
  coordinateEquiv (B ⊗[A] C) (Algebra.TensorProduct.includeLeftRingHom Q.generator)
    (by rw [hQ, map_natCast])

/-- 比較は左脚を通常テンソルの完備化の左脚に送る。 -/
theorem crystallineCompletedTensorRingEquiv_left (b : B) :
    crystallineCompletedTensorRingEquiv Q hQ (prismCompletedTensorLeft Q b) =
      principalCompletionRingCatUnit p (CommRingCat.of (B ⊗[A] C)) (b ⊗ₜ[A] (1 : C)) :=
  coordinateEquiv_unit (B ⊗[A] C) (Algebra.TensorProduct.includeLeftRingHom Q.generator)
    (by rw [hQ, map_natCast]) (b ⊗ₜ[A] (1 : C))

/-- 比較は右脚を通常テンソルの完備化の右脚に送る。 -/
theorem crystallineCompletedTensorRingEquiv_right (c : C) :
    crystallineCompletedTensorRingEquiv Q hQ (prismCompletedTensorRight Q c) =
      principalCompletionRingCatUnit p (CommRingCat.of (B ⊗[A] C)) ((1 : B) ⊗ₜ[A] c) :=
  coordinateEquiv_unit (B ⊗[A] C) (Algebra.TensorProduct.includeLeftRingHom Q.generator)
    (by rw [hQ, map_natCast]) ((1 : B) ⊗ₜ[A] c)

end SerrePositivity.BhattScholze.Prismatic
