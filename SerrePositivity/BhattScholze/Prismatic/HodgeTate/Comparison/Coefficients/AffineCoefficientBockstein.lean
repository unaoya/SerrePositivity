module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCoefficientDiagram
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZero
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCoefficientDiagram
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZero

/-!
# 生成元を保つ affine 係数変更と標準 Bockstein

## 概要
元の affine 模型の係数変更が、実際の Hodge–Tate Bockstein と可換であることを示す。

## 方針
Bockstein の代表元公式で補助係数環への非依存を確認し、既存の自然性を使う。

## 規約
選択生成元の厳密な保存を要求する。単元倍を係数 1 として扱わない。

## 使われ方
Zp から特定の普遍結晶被覆への標準係数射の、次数一の比較。
-/

public noncomputable section
universe u
open CategoryTheory
open SerrePositivity.Cosimplicial
namespace SerrePositivity.BhattScholze.Prismatic

/-- 補助的な係数環を替えても、同じ正則元による Bockstein の台の加法写像は同じ。 -/
theorem affineCupBockstein_coefficients
    (C : CosimplicialObject CommRingCat.{u}) (d : ∀ n, C.obj n)
    (hd : ∀ {m n} (θ : m ⟶ n), C.map θ (d m) = d n)
    (hr : ∀ n, Function.Injective (fun x : C.obj n => d n * x))
    (k l : Type u) [CommRing k] [CommRing l]
    (ιk : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ C)
    (ιl : (Functor.const SimplexCategory).obj (CommRingCat.of l) ⟶ C)
    (i : ℕ) (a : cohomology (quotPow C d hd 1) i) :
    cupBockstein C d hd hr k ιk i a = cupBockstein C d hd hr l ιl i a := by
  obtain ⟨a, rfl⟩ := cohomologyClass_surjective (quotPow C d hd 1) i a
  obtain ⟨x, y, hx, hy⟩ := exists_regularCocycleLift C d hd i a
  let b := projectCycle C d hd (i + 1) y
    (cochainDifferential_eq_zero_of_eq_mul C d hd hr i x y hy)
  exact (cupBockstein_class C d hd hr k ιk i a b x y hx rfl hy).trans
    (cupBockstein_class C d hd hr l ιl i a b x y hx rfl hy).symm

variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (r : ℕ)

/-- 生成元を保つ元の係数変更は、元の Hodge–Tate Bockstein と可換。 -/
theorem affineHTCoefficientReduced_bockstein
    (hg : f.toRingHom P.generator = Q.generator) (i : ℕ)
    (a : hodgeTateCohomology' P hP r i) :
    cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r hg) (i + 1)
        (bockstein P hP r i a) =
      bockstein Q hQ r i
        (cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r hg) i a) := by
  exact (bockstein_natural (htRings P hP r) (htGenerator P hP r)
    (htGenerator_nat P hP r) (htGenerator_regular P hP r) A (htBase P hP r)
    (htRings Q hQ r) (htGenerator Q hQ r) (htGenerator_nat Q hQ r)
    (htGenerator_regular Q hQ r) (affineHTCoefficientRings f hP hQ r)
    (affineHTCoefficientRings_generator f hP hQ r hg) i a).trans
      (affineCupBockstein_coefficients (htRings Q hQ r) (htGenerator Q hQ r)
        (htGenerator_nat Q hQ r) (htGenerator_regular Q hQ r) A B
        (htBase P hP r ≫ affineHTCoefficientRings f hP hQ r)
        (htBase Q hQ r) i _)

end SerrePositivity.BhattScholze.Prismatic
