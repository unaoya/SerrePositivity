module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittFiniteBridge
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittFiniteBridge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittSmallFrame
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDEnvelopeCrystalline
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittCrystallinePrism

/-!
# 有限枠の結晶の橋の余単体自然性

## 概要
各次数の有限 Witt の橋を、固定した有限枠の余単体射にまとめる。

## 方針
有限包の二つの合成が、係数の ψ と各頂点の変数の p 乗で一致することを使う。
最後に標準の小さい完備分冪模型へ移す。

## 規約
多項式代数と有限枠は固定し、余単体の添字を変える。

## 使われ方
BS 著者版 Theorem 6.4 の Witt の橋の有限枠への帰着。
-/

public noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic.WittFiniteBridge

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hpC : Function.Injective (fun x : A ⧸ P.ideal => (p : A ⧸ P.ideal) * x))
variable (hloc : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A ⧸ P.ideal))
variable (hk : IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal))
variable [IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)]
variable (Q : Poly (A ⧸ P.ideal))

local notation "C" => (A ⧸ P.ideal)
local notation "W" => WittVector p C
local notation "γ" => wittPdStructure p C hpC hloc
local notation "hpW" => p_mem_wittPdIdeal p C
local notation "D" n => PDCechNerve.term p γ hpW (smallResidue_ker P Q) (smallFrame P Q) n
local notation "reg" n => regular P hpC hloc hk Q n
local notation "T" n => wittPDEnvelopeCrystalline hpC hloc (D n) (reg n)
local notation "b" n => OrientedPrism.Hom.comp
  (wittPDEnvelopeCrystallineBase hpC hloc (D n) (reg n)) (psiPrism P hpA hpC)
variable {κ : Cardinal.{u}} {m n : ℕ}

private abbrev prismBridge (n : ℕ) (X : AffineEnvelopeTerm P Q.n n κ) : X.X.B →+* (D n).carrier :=
  (existsUnique_at P hpA hpC hloc hk Q n X).choose

private abbrev target (θ : ⦋m⦌ ⟶ ⦋n⦌) : (D m).carrier →ₐ[W] (D n).carrier :=
  PDCechNerve.mapCopies p γ hpW (smallResidue_ker P Q) (smallFrame P Q) θ.toOrderHom

private theorem target_delta (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (T m).deltaStructure.IsDeltaHom (T n).deltaStructure (target P hpC hloc Q θ).toRingHom := by
  apply wittPDEnvelopeCrystalline_isDeltaHom hpC hloc (D m) (D n) (reg m) (reg n)
    (target P hpC hloc Q θ)
    (PDCechNerve.mapCopies_isDPMorphism p γ hpW (smallResidue_ker P Q) (smallFrame P Q) θ.toOrderHom)
    (fun ji => (ji.1, θ.toOrderHom ji.2))
  intro ji
  exact PDCechNerve.mapCopies_variableImage p γ hpW (smallResidue_ker P Q) (smallFrame P Q)
    θ.toOrderHom ji

private theorem naturality (U : AffineEnvelopeTerm P Q.n m κ)
    (V : AffineEnvelopeTerm P Q.n n κ) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (prismBridge P hpA hpC hloc hk Q n V).comp (affineTermMap P U V θ).toHom.toRingHom =
      (target P hpC hloc Q θ).toRingHom.comp (prismBridge P hpA hpC hloc hk Q m U) := by
  let f := (prismBridge P hpA hpC hloc hk Q n V).comp (affineTermMap P U V θ).toHom.toRingHom
  let g := (target P hpC hloc Q θ).toRingHom.comp (prismBridge P hpA hpC hloc hk Q m U)
  have hU := (existsUnique_at P hpA hpC hloc hk Q m U).choose_spec.1
  have hV := (existsUnique_at P hpA hpC hloc hk Q n V).choose_spec.1
  have hf : U.X.Q.deltaStructure.IsDeltaHom (T n).deltaStructure f :=
    hV.1.comp (affineTermMap P U V θ).toHom.map_delta
  have hg : U.X.Q.deltaStructure.IsDeltaHom (T n).deltaStructure g :=
    (target_delta P hpC hloc hk Q θ).comp hU.1
  have hfb : f.comp U.X.toHom.toRingHom = (b n).toRingHom := by
    unfold f
    rw [RingHom.comp_assoc]
    change (prismBridge P hpA hpC hloc hk Q n V).comp (((affineTermMap P U V θ).toHom.comp U.X.toHom).toRingHom) = _
    rw [(affineTermMap P U V θ).comm_base, hV.2.1]
  have hgb : g.comp U.X.toHom.toRingHom = (b n).toRingHom := by
    unfold g
    rw [RingHom.comp_assoc, hU.2.1]
    apply RingHom.ext
    intro x
    change target P hpC hloc Q θ (algebraMap W (D m).carrier (psiRing P hpA x)) =
      algebraMap W (D n).carrier (psiRing P hpA x)
    exact (target P hpC hloc Q θ).commutes _
  have hv (j : Fin Q.n) (i : Fin (m + 1)) :
      f (U.η (affineVariable P Q.n m j i)) =
        g (U.η (affineVariable P Q.n m j i)) := by
    unfold f g
    rw [RingHom.comp_apply, RingHom.comp_apply, affineTermMap_apply, hV.2.2, hU.2.2, map_pow]
    exact congrArg (fun z : (D n).carrier => z ^ p)
      (PDCechNerve.mapCopies_variableImage p γ hpW (smallResidue_ker P Q) (smallFrame P Q)
        θ.toOrderHom (ULift.up j, i)).symm
  have hI : U.X.Q.ideal ≤ (T n).ideal.comap f := by
    rw [U.envelope.ideal_eq, Ideal.span_singleton_le_iff_mem]
    change (f.comp (U.η.comp (completedFreeDeltaBase P _))) P.generator ∈ (T n).ideal
    rw [U.base_eq, hfb]
    exact (b n).map_generator_mem
  have hmod (j : Fin Q.n) (i : Fin (m + 1)) :
      Ideal.Quotient.mk (T n).ideal (f (U.η (affineVariable P Q.n m j i))) =
        Ideal.Quotient.mk (T n).ideal (f (U.η (affineVariable P Q.n m j 0))) := by
    apply Ideal.Quotient.eq.mpr
    rw [← map_sub]
    exact hI (affineTerm_difference_mem P U j i 0)
  apply (U.existsUnique_liftVariables (T n) (b n) _ hmod).unique
  · exact ⟨hf, hfb, fun _ _ => rfl⟩
  · exact ⟨hg, hgb, fun j i => (hv j i).symm⟩

variable (U : ∀ n, AffineEnvelopeTerm P Q.n n κ)

local notation "res" => Under.map (CommRingCat.ofHom (psiRing P hpA))

private def bridgeToNerve :
    polyCosimplicialAlgebraOfAffineTerms P U ⟶
      pdCechNerve p γ hpW (smallResidue_ker P Q) (smallFrame P Q) ⋙ res where
  app n := Under.homMk (CommRingCat.ofHom (prismBridge P hpA hpC hloc hk Q n.len (U n.len)))
    (CommRingCat.hom_ext (existsUnique_at P hpA hpC hloc hk Q n.len (U n.len)).choose_spec.1.2.1)
  naturality {m n} θ := by
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    exact naturality P hpA hpC hloc hk Q (U m.len) (U n.len) θ

/-- 有限 prismatic 枠から小さい Witt 模型への余単体的な結晶の橋。 -/
def finiteBridge :
    polyCosimplicialAlgebraOfAffineTerms P U ⟶ pdModel p W Q.n ⋙ res :=
  bridgeToNerve P hpA hpC hloc hk Q U ≫
    Functor.whiskerRight (smallIso P hpC hloc Q hk).inv res

end SerrePositivity.BhattScholze.Prismatic.WittFiniteBridge
