module

public import SerrePositivity.BhattScholze.Prismatic.CrystallinePDQuotientLift
public import SerrePositivity.CategoryTheory.ProCechNerveData
import all SerrePositivity.BhattScholze.Prismatic.CrystallinePDQuotientLift
import all SerrePositivity.BhattScholze.Prismatic.CrystallinePDQuotient
import all SerrePositivity.BhattScholze.Prismatic.PDAdicCompletion
import all SerrePositivity.BhattScholze.Prismatic.CrystallineSiteBasic

/-!
# 分冪環の有限冪商の塔

## 概要
p^{e+2} 商の遷移を厚化の射として作り、環の向きとサイトの向きで塔を得る。

## 方針
商の普遍性で射を作り、代表元の上の公式から関手則を示す。

## 規約
環の向きは ℕᵒᵖ、サイトの向きは ℕ。pro 弱終性には元の分冪環からの持ち上げを明示する。

## 使われ方
Berthelot III.4、Stacks 07HP。分冪包の塔の pro 弱終性の最後の降下。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable (R : Type u) [CommRing R] [Algebra (k ⧸ J) R]
variable {D : Type u} [CommRing D] [Algebra k D] {I : Ideal D} (δ : DividedPowers I)
variable (hp : (p : D) ∈ I) (hbase : DividedPowers.IsDPMorphism γ δ (algebraMap k D))
variable (sec : R →+* D ⧸ I)
variable (hsec : sec.comp ((algebraMap (k ⧸ J) R).comp (Ideal.Quotient.mk J)) =
  (Ideal.Quotient.mk I).comp (algebraMap k D))
variable {κ : Cardinal.{u}} (hsmall : Cardinal.mk D ≤ κ)
local notation "P" => Ideal.span {(p : D)}
local notation "Q" e => crystallinePDQuotient p γ R δ hp hbase sec hsec hsmall e

private theorem quotientPrimePow_zero (a : ℕ) : (p : (Q a).B) ^ (a + 2) = 0 := by
  change (Ideal.Quotient.mk (P ^ (a + 2)) (p : D)) ^ (a + 2) = 0
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self (p : D)) _

private theorem quotientUnit_dp (a : ℕ) :
    δ.IsDPMorphism (Q a).δ (Ideal.Quotient.mk (P ^ (a + 2))) := by
  change δ.IsDPMorphism (PDAdicCompletion.quotientDividedPowers p δ hp a) _
  exact DividedPowers.Quotient.isDPMorphism _ _

/-- 大きい指数の商から小さい指数の商への、分冪と剰余を保つ射。 -/
def crystallinePDQuotientTransition (a b : ℕ) (h : a ≤ b) : (Q b) ⟶ (Q a) :=
  crystallinePDQuotientLift p γ R δ hp hbase sec hsec hsmall (Q a) b
    (Ideal.Quotient.mkₐ k (P ^ (a + 2)))
    (quotientUnit_dp p γ R δ hp hbase sec hsec hsmall a)
    (pow_eq_zero_of_le (Nat.add_le_add_right h 2)
      (quotientPrimePow_zero p γ R δ hp hbase sec hsec hsmall a)) rfl

/-- 遷移射は実際に代表元を同じ代表元へ送る。 -/
@[simp] theorem crystallinePDQuotientTransition_mk (a b : ℕ) (h : a ≤ b) (x : D) :
    (crystallinePDQuotientTransition p γ R δ hp hbase sec hsec hsmall a b h).toAlgHom
      (Ideal.Quotient.mk (P ^ (b + 2)) x) = Ideal.Quotient.mk (P ^ (a + 2)) x := by
  dsimp only [crystallinePDQuotientTransition, crystallinePDQuotientLift,
    crystallinePDQuotientLiftAlg]
  rfl

/-- 商からの厚化の射は元の環の代表元上で判定できる。 -/
theorem crystallinePDQuotient_hom_ext (e : ℕ) {X : CrysOver p γ R κ}
    {f g : (Q e) ⟶ X} (h : ∀ x : D,
      f.toAlgHom (Ideal.Quotient.mk (P ^ (e + 2)) x) =
      g.toAlgHom (Ideal.Quotient.mk (P ^ (e + 2)) x)) : f = g := by
  apply CrysOver.Hom.ext p
  apply AlgHom.ext
  intro b
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact h x

/-- 環の向きの有限 p 冪商の塔。 -/
def crystallinePDQuotientTower : ℕᵒᵖ ⥤ CrysOver p γ R κ where
  obj e := Q e.unop
  map {a b} f := crystallinePDQuotientTransition p γ R δ hp hbase sec hsec hsmall
    b.unop a.unop (leOfHom f.unop)
  map_id e := by
    apply crystallinePDQuotient_hom_ext p γ R δ hp hbase sec hsec hsmall e.unop
    intro x
    rw [crystallinePDQuotientTransition_mk]
    rfl
  map_comp {a b c} f g := by
    apply crystallinePDQuotient_hom_ext p γ R δ hp hbase sec hsec hsmall _
    intro x
    change (crystallinePDQuotientTransition p γ R δ hp hbase sec hsec hsmall
      c.unop a.unop (leOfHom (f ≫ g).unop)).toAlgHom
        (Ideal.Quotient.mk (P ^ (a.unop + 2)) x) =
      (crystallinePDQuotientTransition p γ R δ hp hbase sec hsec hsmall
        c.unop b.unop (leOfHom g.unop)).toAlgHom
          ((crystallinePDQuotientTransition p γ R δ hp hbase sec hsec hsmall
            b.unop a.unop (leOfHom f.unop)).toAlgHom
              (Ideal.Quotient.mk (P ^ (a.unop + 2)) x))
    rw [crystallinePDQuotientTransition_mk, crystallinePDQuotientTransition_mk,
      crystallinePDQuotientTransition_mk]

/-- サイトの向きの塔。 -/
def crystallinePDQuotientSiteTower : ℕ ⥤ (CrysOver p γ R κ)ᵒᵖ :=
  (crystallinePDQuotientTower p γ R δ hp hbase sec hsec hsmall).rightOp

/-- 分冪環からの持ち上げは、有限冪商の塔の pro 弱終性を与える。 -/
theorem crystallinePDQuotientSiteTower_proWeaklyTerminal
    (hlift : ∀ X : CrysOver p γ R κ, ∃ f : D →ₐ[k] X.B,
      ∃ hf : DividedPowers.IsDPMorphism δ X.δ f.toRingHom,
      (Ideal.quotientMap X.JB f.toRingHom
        (Ideal.map_le_iff_le_comap.mp hf.ideal_comp)).comp sec = X.sec) :
    IsProWeaklyTerminal (crystallinePDQuotientSiteTower p γ R δ hp hbase sec hsec hsmall) := by
  intro V
  obtain ⟨f, hf, hc⟩ := hlift V.unop
  obtain ⟨N, hN⟩ := V.unop.nilpotent
  refine ⟨N, ⟨?_⟩⟩
  exact (crystallinePDQuotientLift p γ R δ hp hbase sec hsec hsmall V.unop N f hf
    (pow_eq_zero_of_le (Nat.le_add_right N 2) hN) hc).op

end SerrePositivity.BhattScholze.Prismatic
