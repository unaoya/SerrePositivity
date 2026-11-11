module

public import SerrePositivity.BhattScholze.Prismatic.PDCechQuotientVariablesLift
public import SerrePositivity.CategoryTheory.CechNerveData
import all SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineCosimplicial
import all SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineQuotient
import all SerrePositivity.BhattScholze.Prismatic.CrystallinePDQuotient
import all SerrePositivity.BhattScholze.Prismatic.CrystallineSiteBasic

/-!
# 結晶 Čech 有限冪商の余積の普遍性

## 概要
各有限段の n 次項は、標準頂点の脚により零次項 n+1 個の余積となる。

## 方針
零次項からの射で頂点変数の像を指定して desc を作り、変数上の判定で一意性を示す。

## 規約
標的で消える p 冪は、零次項からの射一本から従う。

## 使われ方
Berthelot III.4、Stacks 07HP。各有限段の実際の Čech データ。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable (hp : (p : k) ∈ J) (R : Type u) [CommRing R] [Algebra (k ⧸ J) R]
variable [Algebra k R] [IsScalarTower k (k ⧸ J) R]
variable {S : Type u} (s : S → R) (hs : Function.Surjective (pdFrameEval (k := k) s 0))
variable {κ : Cardinal.{u}}
variable (hsmall : ∀ n, Cardinal.mk
  (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s n).carrier ≤ κ)
variable (e : ℕ)

private theorem leg_prime_zero (X : CrysOver p γ R κ)
    (f : pdCechQuotient p γ hp R s hs hsmall e 0 ⟶ X) :
    (p : X.B) ^ (e + 2) = 0 := by
  have h : (p : (pdCechQuotient p γ hp R s hs hsmall e 0).B) ^ (e + 2) = 0 := by
    change (Ideal.Quotient.mk _ (p :
      (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s 0).carrier)) ^
        (e + 2) = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _
  simpa only [map_pow, map_natCast, map_zero] using congrArg f.toAlgHom h

private theorem desc_exists (n : ℕ) (X : CrysOver p γ R κ)
    (f : Fin (n + 1) → (pdCechQuotient p γ hp R s hs hsmall e 0 ⟶ X)) :
    ∃ g : pdCechQuotient p γ hp R s hs hsmall e n ⟶ X,
      ∀ (x : S) (i : Fin (n + 1)),
        g.toAlgHom (pdCechQuotientVariable p γ hp R s hs hsmall e n (x, i)) =
          (f i).toAlgHom (pdCechQuotientVariable p γ hp R s hs hsmall e 0 (x, 0)) := by
  let v : S × Fin (n + 1) → X.B := fun a =>
    (f a.2).toAlgHom (pdCechQuotientVariable p γ hp R s hs hsmall e 0 (a.1, 0))
  have hv : ∀ a, Ideal.Quotient.mk X.JB (v a) = X.sec (s a.1) := by
    intro a
    exact (f a.2).comm_sec (s a.1) _
      (pdCechQuotientVariable_residue p γ hp R s hs hsmall e 0 (a.1, 0))
  obtain ⟨g, hg, _⟩ := existsUnique_pdCechQuotientVariablesLift p γ hp R s hs hsmall e n X v hv
    (leg_prime_zero p γ hp R s hs hsmall e X (f 0))
  exact ⟨g, fun x i => hg (x, i)⟩

/-- 頂点ごとの射をまとめた、有限段の Čech 余積の desc。 -/
def pdCechQuotientCoproductDesc (n : ℕ) (X : CrysOver p γ R κ)
    (f : Fin (n + 1) → (pdCechQuotient p γ hp R s hs hsmall e 0 ⟶ X)) :
    pdCechQuotient p γ hp R s hs hsmall e n ⟶ X :=
  (desc_exists p γ hp R s hs hsmall e n X f).choose

/-- desc は各頂点変数を指定された射の像へ送る。 -/
theorem pdCechQuotientCoproductDesc_variable (n : ℕ) (X : CrysOver p γ R κ)
    (f : Fin (n + 1) → (pdCechQuotient p γ hp R s hs hsmall e 0 ⟶ X))
    (x : S) (i : Fin (n + 1)) :
    (pdCechQuotientCoproductDesc p γ hp R s hs hsmall e n X f).toAlgHom
      (pdCechQuotientVariable p γ hp R s hs hsmall e n (x, i)) =
        (f i).toAlgHom (pdCechQuotientVariable p γ hp R s hs hsmall e 0 (x, 0)) :=
  (desc_exists p γ hp R s hs hsmall e n X f).choose_spec x i

/-- 標準頂点の脚は各有限段の n 次項を零次項 n+1 個の余積にする。 -/
def pdCechQuotient_isCoproduct (n : ℕ) :
    IsColimit (Cofan.mk ((pdCechQuotientCosimplicial p γ hp R s hs hsmall e).obj ⦋n⦌)
      (fun i : Fin (n + 1) =>
        (pdCechQuotientCosimplicial p γ hp R s hs hsmall e).map
          (SimplexCategory.const ⦋0⦌ ⦋n⦌ i))) := by
  refine Cofan.IsColimit.mk _
    (fun c => pdCechQuotientCoproductDesc p γ hp R s hs hsmall e n c.pt c.inj) ?_ ?_
  · intro c i
    apply pdCechQuotient_hom_ext_variables p γ hp R s hs hsmall e 0
    intro x
    change (pdCechQuotientCoproductDesc p γ hp R s hs hsmall e n c.pt c.inj).toAlgHom
      ((pdCechQuotientMap p γ hp R s hs hsmall e (fun _ : Fin 1 => i)).toAlgHom
        (pdCechQuotientVariable p γ hp R s hs hsmall e 0 x)) =
          (c.inj i).toAlgHom (pdCechQuotientVariable p γ hp R s hs hsmall e 0 x)
    rw [pdCechQuotientVariable_map, pdCechQuotientCoproductDesc_variable]
    exact congrArg (fun a => (c.inj i).toAlgHom
      (pdCechQuotientVariable p γ hp R s hs hsmall e 0 a))
        (Prod.ext rfl (by apply Fin.ext; omega))
  · intro c g hg
    apply pdCechQuotient_hom_ext_variables p γ hp R s hs hsmall e n
    rintro ⟨x, i⟩
    have h := congrArg (fun a : pdCechQuotient p γ hp R s hs hsmall e 0 ⟶ c.pt =>
      a.toAlgHom (pdCechQuotientVariable p γ hp R s hs hsmall e 0 (x, 0))) (hg i)
    change g.toAlgHom
      ((pdCechQuotientMap p γ hp R s hs hsmall e (fun _ : Fin 1 => i)).toAlgHom
        (pdCechQuotientVariable p γ hp R s hs hsmall e 0 (x, 0))) = _ at h
    rw [pdCechQuotientVariable_map] at h
    exact h.trans
      (pdCechQuotientCoproductDesc_variable p γ hp R s hs hsmall e n c.pt c.inj x i).symm

/-- 各有限段をサイトの向きの、指定された有限冪を持つ Čech データへ移す。 -/
def pdCechQuotientCechData : CechNerveData
    (Opposite.op (pdCechQuotient p γ hp R s hs hsmall e 0)) :=
  CechNerveData.ofCoproducts (pdCechQuotientCosimplicial p γ hp R s hs hsmall e)
    (pdCechQuotient_isCoproduct p γ hp R s hs hsmall e)

end SerrePositivity.BhattScholze.Prismatic
