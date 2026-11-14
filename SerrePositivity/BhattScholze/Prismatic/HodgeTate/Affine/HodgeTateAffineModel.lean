module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps

/-!
# Hodge–Tate 比較の affine 余単体模型

## 概要
affine Čech–Alexander 模型の台の余単体的環とその生成元による商を取り出す。

## 方針
基底からの構造射と、prism 射が生成元の主イデアルを保つことを使う。

## 規約
商は各余単体次数で取る。

## 使われ方
多項式の場合の Hodge–Tate 写像と結晶比較。
-/

public noncomputable section

universe u

open CategoryTheory
open SerrePositivity.Cosimplicial
open scoped Simplicial

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
    (hP : IsBoundedPrism P) (r : ℕ)

/-- 基底の剰余環上の完備多項式環。 -/
abbrev affineAlgebra := prismPolynomialCompletion P (Fin r)

/-- 小さい affine Čech–Alexander 模型。 -/
abbrev htCech := cechAlexanderAffine P hP r (cutoff A (affineAlgebra P r)) le_rfl

/-- affine Čech–Alexander 模型の台の余単体的可換環。 -/
abbrev htRings : CosimplicialObject CommRingCat.{u} :=
  polyCosimplicialAlgebra P hP r ⋙ Under.forget (CommRingCat.of A)

/-- 各項の基底からの構造射。 -/
def htBase : (Functor.const SimplexCategory).obj (CommRingCat.of A) ⟶ htRings P hP r where
  app n := CommRingCat.ofHom ((htCech P hP r).obj n).toHom.toRingHom
  naturality m n θ := by
    let f := (polyCosimplicialAlgebra P hP r).map θ
    exact (Category.id_comp _).trans (Under.w f).symm

/-- 選んだ基底生成元の各項での像。 -/
abbrev htGenerator (n : SimplexCategory) : (htRings P hP r).obj n :=
  (htBase P hP r).app n P.generator

theorem htGenerator_nat {m n : SimplexCategory} (θ : m ⟶ n) :
    (htRings P hP r).map θ (htGenerator P hP r m) = htGenerator P hP r n := by
  have h := (htBase P hP r).naturality θ
  change (𝟙 _ ≫ _) = _ at h
  rw [Category.id_comp] at h
  exact ConcreteCategory.congr_hom h.symm P.generator

private theorem htGenerator_ideal (n : SimplexCategory) :
    Ideal.span {htGenerator P hP r n} = ((htCech P hP r).obj n).Q.ideal := by
  let f := ((htCech P hP r).obj n).toHom
  have h := f.map_ideal_eq
  change (Ideal.span {P.generator}).map f.toRingHom = _ at h
  rw [Ideal.map_span, Set.image_singleton] at h
  exact h

/-- 基底生成元の像での乗法は各項で単射。 -/
theorem htGenerator_regular (n : SimplexCategory) :
    Function.Injective (fun x => htGenerator P hP r n * x) := by
  let X := (htCech P hP r).obj n
  let d : X.B := htGenerator P hP r n
  have hI : Ideal.span {d} = X.Q.ideal := htGenerator_ideal P hP r n
  have hmem : X.Q.generator ∈ Ideal.span {d} := by
    rw [hI]
    exact Ideal.subset_span rfl
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hmem
  intro x y hxy
  let x' : X.B := x
  let y' : X.B := y
  have hxy' : d * x' = d * y' := hxy
  change x' = y'
  apply X.Q.generator_regular
  change X.Q.generator * x' = X.Q.generator * y'
  rw [hb, mul_right_comm d b x', mul_right_comm d b y', hxy']

/-- affine 模型の基底生成元による項ごとの商。 -/
abbrev reducedModel := quotPow (htRings P hP r) (htGenerator P hP r) (htGenerator_nat P hP r) 1

/-- 基底生成元による商と、各 prism の剰余環との同一視。 -/
def htResidueIso (n : SimplexCategory) :
    let X := (htCech P hP r).obj n
    (reducedModel P hP r).obj n ≃+* X.B ⧸ X.Q.ideal := by
  change ((htRings P hP r).obj n ⧸ Ideal.span {htGenerator P hP r n ^ (1 : ℕ)}) ≃+* _
  let X := (htCech P hP r).obj n
  let d : X.B := htGenerator P hP r n
  let I : Ideal X.B := Ideal.span {d ^ (1 : ℕ)}
  change (X.B ⧸ I) ≃+* (X.B ⧸ X.Q.ideal)
  exact Ideal.quotEquivOfEq (show I = X.Q.ideal by
    change Ideal.span {d ^ (1 : ℕ)} = _
    rw [pow_one]
    exact htGenerator_ideal P hP r n)

/-- 基底の完備多項式環から各項の剰余環への射。 -/
def htSec (n : SimplexCategory) : affineAlgebra P r →+* (reducedModel P hP r).obj n :=
  (htResidueIso P hP r n).symm.toRingHom.comp ((htCech P hP r).obj n).sec

end SerrePositivity.BhattScholze.Prismatic
