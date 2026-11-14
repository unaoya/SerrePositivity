module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PolynomialFrobeniusCech
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PolynomialFrobeniusCech
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient

/-!
# 結晶比較の Čech 座標

## 概要
完備自由 δ 環の構造射を mod p に降ろし、多項式 Čech 余脈体から
Hodge–Tate 模型への自然変換を得る。

## 方針
初期座標は affine envelope の単位で送り、高次座標には δ の反復を使う。

## 規約
変数の添字は多項式変数、δ の反復次数、Čech の頂点の組。

## 使われ方
Frobenius に沿う結晶比較の押し出し。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
    (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

private def term (n : SimplexCategory) := affineEnvelopeTerm P hP r n.len (polyCutoff P r) le_rfl

private def coord (n : SimplexCategory) (j : Fin r) (i : Fin (n.len + 1)) (a : ℕ) :
    (htRings P hP r).obj n :=
  let T := term P hP r n
  T.X.Q.deltaStructure.delta^[a] (T.η (affineVariable P r n.len j i))

private theorem coord_nat {m n : SimplexCategory} (θ : m ⟶ n)
    (j : Fin r) (i : Fin (m.len + 1)) (a : ℕ) :
    (htRings P hP r).map θ (coord P hP r m j i a) =
      coord P hP r n j (θ.toOrderHom i) a := by
  let M := term P hP r m
  let N := term P hP r n
  let f := affineTermMap P M N θ
  let x := M.η (affineVariable P r m.len j i)
  let y := N.η (affineVariable P r n.len j (θ.toOrderHom i))
  change f.toHom.toRingHom (M.X.Q.deltaStructure.delta^[a] x) =
    N.X.Q.deltaStructure.delta^[a] y
  induction a with
  | zero => exact affineTermMap_apply P M N θ j i
  | succ a ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        f.toHom.map_delta, ih]

private def project := quotProjection (htRings P hP r) (htGenerator P hP r)
  (htGenerator_nat P hP r) 1

private def residueCoeff (n : SimplexCategory) :
    (A ⧸ P.ideal) →+* (reducedModel P hP r).obj n :=
  Ideal.Quotient.lift _ (((project P hP r).app n).hom.comp ((htBase P hP r).app n).hom) (by
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change ((htBase P hP r).app n).hom a ∈ Ideal.span {htGenerator P hP r n ^ (1 : ℕ)}
    rw [pow_one]
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))

private theorem residueCoeff_mk (n : SimplexCategory) (a : A) :
    residueCoeff P hP r n (Ideal.Quotient.mk P.ideal a) =
      (project P hP r).app n ((htBase P hP r).app n a) := rfl

private theorem residueCoeff_nat {m n : SimplexCategory} (θ : m ⟶ n) (a : A ⧸ P.ideal) :
    (reducedModel P hP r).map θ (residueCoeff P hP r m a) = residueCoeff P hP r n a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [residueCoeff_mk, residueCoeff_mk]
  have h := ConcreteCategory.congr_hom ((project P hP r).naturality θ).symm
    ((htBase P hP r).app m a)
  change (reducedModel P hP r).map θ
    ((project P hP r).app m ((htBase P hP r).app m a)) =
    (project P hP r).app n ((htRings P hP r).map θ ((htBase P hP r).app m a)) at h
  rw [h]
  congr 1
  have hh := (htBase P hP r).naturality θ
  change 𝟙 _ ≫ _ = _ at hh
  rw [Category.id_comp] at hh
  exact ConcreteCategory.congr_hom hh.symm a

private theorem residueCoord_nat {m n : SimplexCategory} (θ : m ⟶ n) (j : Fin r)
    (i : Fin (m.len + 1)) (a : ℕ) :
    (reducedModel P hP r).map θ ((project P hP r).app m (coord P hP r m j i a)) =
      (project P hP r).app n (coord P hP r n j (θ.toOrderHom i) a) := by
  have h := ConcreteCategory.congr_hom ((project P hP r).naturality θ).symm (coord P hP r m j i a)
  change (reducedModel P hP r).map θ
    ((project P hP r).app m (coord P hP r m j i a)) =
    (project P hP r).app n ((htRings P hP r).map θ (coord P hP r m j i a)) at h
  rw [h, coord_nat]

private abbrev PolyTerm (n : SimplexCategory) :=
  MvPolynomial ((Fin r × ℕ) × Fin (n.len + 1)) (A ⧸ P.ideal)

private def polyToResidueApp (n : SimplexCategory) :
    PolyTerm P r n →+* (reducedModel P hP r).obj n :=
  MvPolynomial.eval₂Hom (residueCoeff P hP r n) (fun t =>
    (project P hP r).app n (coord P hP r n t.1.1 t.2 t.1.2))

private theorem polyToResidueApp_C (n : SimplexCategory) (a : A ⧸ P.ideal) :
    polyToResidueApp P hP r n (MvPolynomial.C a) = residueCoeff P hP r n a :=
  MvPolynomial.eval₂Hom_C _ _ _

private theorem polyToResidueApp_X (n : SimplexCategory)
    (t : (Fin r × ℕ) × Fin (n.len + 1)) :
    polyToResidueApp P hP r n (MvPolynomial.X t) =
      (project P hP r).app n (coord P hP r n t.1.1 t.2 t.1.2) :=
  MvPolynomial.eval₂Hom_X' _ _ _

private def polyToResidue :
    polynomialCech (A ⧸ P.ideal) (Fin r × ℕ) ⟶ reducedModel P hP r where
  app n := CommRingCat.ofHom (polyToResidueApp P hP r n)
  naturality m n θ := by
    let ρ : (Fin r × ℕ) × Fin (m.len + 1) → (Fin r × ℕ) × Fin (n.len + 1) :=
      fun t => (t.1, θ.toOrderHom t.2)
    let L := (polyToResidueApp P hP r n).comp (MvPolynomial.rename (R := A ⧸ P.ideal) ρ).toRingHom
    let R := ((reducedModel P hP r).map θ).hom.comp (polyToResidueApp P hP r m)
    apply CommRingCat.hom_ext
    change L = R
    apply MvPolynomial.ringHom_ext'
    · apply RingHom.ext
      intro a
      change polyToResidueApp P hP r n (MvPolynomial.rename ρ (MvPolynomial.C a)) =
        (reducedModel P hP r).map θ (polyToResidueApp P hP r m (MvPolynomial.C a))
      rw [MvPolynomial.rename_C, polyToResidueApp_C, polyToResidueApp_C]
      exact (residueCoeff_nat P hP r θ a).symm
    · rintro ⟨⟨j, a⟩, i⟩
      change polyToResidueApp P hP r n (MvPolynomial.rename ρ (MvPolynomial.X ((j, a), i))) =
        (reducedModel P hP r).map θ (polyToResidueApp P hP r m (MvPolynomial.X ((j, a), i)))
      rw [MvPolynomial.rename_X, polyToResidueApp_X, polyToResidueApp_X]
      exact (residueCoord_nat P hP r θ j i a).symm

/-- 結晶基底で、自由 δ 座標を mod p の affine 模型に送る。 -/
def deltaCoordinatesModP (p : ℕ) [Fact p.Prime] (r : ℕ) :
    polynomialCech (cartierBase.{u} p) (Fin r × ℕ) ⟶
      reducedModel (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r :=
  polyToResidue (crystallineBasePrism p) (crystallineBaseBounded p) r

end SerrePositivity.BhattScholze.Prismatic
