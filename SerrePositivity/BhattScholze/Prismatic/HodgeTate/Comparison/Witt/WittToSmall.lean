module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.BigPDModel
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDPolynomialFunctor
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.BigCechCompletionLift
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PolynomialCompletionResidue
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.AffinePolynomial
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.BigPDModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDPolynomialFunctor
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# Witt 係数の大きい枠から剰余係数の有限枠へ

## 概要
Witt 係数の分冪 Čech 脈体から、第 0 Witt 成分に沿って係数を制限した有限枠へ写す。

## 方針
各頂点で多項式の評価を完備多項式の評価に延長し、大きい枠の変数の像とする。
剰余への写像との一致から分冪包の普遍性を適用する。

## 規約
係数の写像は `wZero`、剰余環の写像は `polynomialResidueEquiv` で表す。

## 使われ方
BS 著者版 Theorem 6.4 の結晶模型の係数変換。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic.WittToSmall

open PDCechNerve
set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

local notation "C" => (A ⧸ P.ideal)
local notation "W" => WittVector p C
local notation "JW" => wittPdIdeal p C
local notation "I" => Ideal.span {(p : C)}

local instance : Algebra W C := (wZero p C).toAlgebra

variable (hpC : Function.Injective (fun x : A ⧸ P.ideal => (p : A ⧸ P.ideal) * x))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A ⧸ P.ideal))
variable (Q : Poly (A ⧸ P.ideal))

local notation "γW" => wittPdStructure p C hpC hlocal
local notation "γC" => residuePdStructure p hpC hlocal
local notation "hpW" => p_mem_wittPdIdeal p C

private theorem hp : (p : C) ∈ I := Ideal.subset_span (Set.mem_singleton _)

local notation "hp'" => hp P
private theorem wittBaseKer : wittPdIdeal p C ≤ RingHom.ker (algebraMap W (bigResidue P Q)) :=
  bigResidue_ker P (J := JW) le_rfl Q

local notation "hJ" => wittBaseKer P Q
local notation "hI" => PDPolynomialFunctor.base_ker (J := I) Q
local notation "small" => PDPolynomialFunctor.frame (J := I) Q
local notation "large" => (Ideal.Quotient.mk (Ideal.span {(p : polyCompletion P Q.n)}))
local notation "D" => term p γC hp' hI small
local notation "E" => term p γW hpW hJ large

private def smallAug (n : ℕ) : (D n).carrier →ₐ[C] MvPolynomial (Fin Q.n) (C ⧸ I) :=
  augmentation p γC hp' hI small n

private def smallAugBig (n : ℕ) : (D n).carrier →+* bigResidue P Q :=
  (polynomialResidueEquiv P hpC Q).toRingHom.comp (smallAug P hpC hlocal Q n).toRingHom

private def eval (n : ℕ) (i : Fin (n + 1)) : polyCompletion P Q.n →+* (D n).carrier :=
  liftFromPolyCompletion p (PDPolynomialFunctor.copyEval p γC hp' Q i).toRingHom
    (by
      let := (D n).isEnvelope.complete
      exact isModuleComplete_of_isAdicComplete _ _ _)

@[simp] private theorem eval_unit (n : ℕ) (i : Fin (n + 1))
    (x : MvPolynomial (Fin Q.n) C) :
    eval P hpC hlocal Q n i (prismPolynomialUnit P (Fin Q.n) x) =
      PDPolynomialFunctor.copyEval p γC hp' Q i x :=
  RingHom.congr_fun
    (liftFromPolyCompletion_comp p (PDPolynomialFunctor.copyEval p γC hp' Q i).toRingHom _) x

private theorem eval_aug (n : ℕ) (i : Fin (n + 1)) :
    (smallAugBig P hpC hlocal Q n).comp (eval P hpC hlocal Q n i) = large := by
  have hz : (p : bigResidue P Q) = 0 := by
    change (Ideal.Quotient.mk _) (p : polyCompletion P Q.n) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  let := isAdicComplete_of_natCast_zero hz
  have hc : IsModuleComplete (bigResidue P Q) (p : bigResidue P Q)
      (ModuleCat.of _ (bigResidue P Q)) :=
    isModuleComplete_of_isAdicComplete _ _ _
  let g := (large).comp (prismPolynomialUnit P (Fin Q.n))
  have h : ((smallAugBig P hpC hlocal Q n).comp (eval P hpC hlocal Q n i)).comp
      (prismPolynomialUnit P (Fin Q.n)) = g := by
    apply RingHom.ext
    intro x
    change smallAugBig P hpC hlocal Q n
      (eval P hpC hlocal Q n i (prismPolynomialUnit P (Fin Q.n) x)) = _
    rw [eval_unit]
    change polynomialResidueEquiv P hpC Q (smallAug P hpC hlocal Q n
      (PDPolynomialFunctor.copyEval p γC hp' Q i x)) = _
    rw [show smallAug P hpC hlocal Q n (PDPolynomialFunctor.copyEval p γC hp' Q i x) =
      MvPolynomial.map (Ideal.Quotient.mk I) x from
      DFunLike.congr_fun (PDPolynomialFunctor.augmentation_copyEval p γC hp' Q i) x]
    exact polynomialResidueEquiv_map P hpC Q x
  exact (liftFromPolyCompletion_unique p g hc _ h).trans
    (liftFromPolyCompletion_unique p g hc large rfl).symm

@[instance_reducible] private def smallWittAlgebra (n : ℕ) : Algebra W (D n).carrier :=
  ((algebraMap C (D n).carrier).comp (wZero p C)).toAlgebra

attribute [local instance] smallWittAlgebra

private def frameMap (n : ℕ) : pdFrame W (polyCompletion P Q.n) n →ₐ[W] (D n).carrier :=
  MvPolynomial.aeval (fun x => eval P hpC hlocal Q n x.2 x.1)

private theorem frameMap_aug (n : ℕ) :
    (smallAugBig P hpC hlocal Q n).comp (frameMap P hpC hlocal Q n).toRingHom =
      (pdFrameEval (k := W) large n).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change smallAugBig P hpC hlocal Q n (frameMap P hpC hlocal Q n
      (algebraMap W _ a)) = pdFrameEval (k := W) large n (algebraMap W _ a)
    rw [AlgHom.commutes, AlgHom.commutes]
    change polynomialResidueEquiv P hpC Q
      (smallAug P hpC hlocal Q n (algebraMap C _ (wZero p C a))) =
        large (algebraMap C _ (wZero p C a))
    rw [AlgHom.commutes]
    change polynomialResidueEquiv P hpC Q (MvPolynomial.C (Ideal.Quotient.mk I (wZero p C a))) =
      large (prismPolynomialUnit P (Fin Q.n) (MvPolynomial.C (wZero p C a)))
    simpa only [MvPolynomial.map_C] using
      polynomialResidueEquiv_map P hpC Q (MvPolynomial.C (wZero p C a))
  · intro x
    change smallAugBig P hpC hlocal Q n (frameMap P hpC hlocal Q n (MvPolynomial.X x)) =
      pdFrameEval (k := W) large n (MvPolynomial.X x)
    rw [frameMap, MvPolynomial.aeval_X, pdFrameEval_X]
    exact RingHom.congr_fun (eval_aug P hpC hlocal Q n x.2) x.1

private theorem frameMap_ker (n : ℕ) :
    (RingHom.ker (pdFrameEval (k := W) large n)).map
      (frameMap P hpC hlocal Q n) ≤ (D n).ideal := by
  rw [Ideal.map_le_iff_le_comap, ← augmentation_ker p γC hp' hI small n]
  intro x hx
  have he := RingHom.congr_fun (frameMap_aug P hpC hlocal Q n) x
  exact (polynomialResidueEquiv P hpC Q).injective (he.trans
    ((RingHom.mem_ker.mp hx).trans (map_zero _).symm))

private theorem wittBasePD (n : ℕ) :
    (γW).IsDPMorphism (D n).dividedPowers (algebraMap W (D n).carrier) :=
  (D n).isEnvelope.base_dp.comp _ (wZero_isDPMorphism p C hpC hlocal)

private def mapAt (n : ℕ) : (E n).carrier →ₐ[W] (D n).carrier :=
  (E n).isEnvelope.liftHom (D n).isEnvelope.complete
    (frameMap P hpC hlocal Q n) (frameMap_ker P hpC hlocal Q n)
    (wittBasePD P hpC hlocal Q n)

private theorem mapAt_isDPMorphism (n : ℕ) :
    (E n).dividedPowers.IsDPMorphism (D n).dividedPowers (mapAt P hpC hlocal Q n).toRingHom :=
  (E n).isEnvelope.liftHom_isDPMorphism ..

private theorem mapAt_X (n : ℕ) (x : polyCompletion P Q.n × Fin (n + 1)) :
    mapAt P hpC hlocal Q n (variableImage p γW hpW hJ large n x) =
      eval P hpC hlocal Q n x.2 x.1 :=
  (DFunLike.congr_fun ((E n).isEnvelope.liftHom_comp ..) (MvPolynomial.X x)).trans
    (MvPolynomial.aeval_X _ _)

private theorem fromCompletion_ext {T : Type u} [CommRing T]
    (hT : IsAdicComplete (Ideal.span {(p : T)}) T)
    {f g : polyCompletion P Q.n →+* T}
    (h : f.comp (prismPolynomialUnit P (Fin Q.n)) =
      g.comp (prismPolynomialUnit P (Fin Q.n))) : f = g := by
  let := hT
  have hc : IsModuleComplete T (p : T) (ModuleCat.of T T) :=
    isModuleComplete_of_isAdicComplete _ _ _
  exact (liftFromPolyCompletion_unique p _ hc f h).trans
    (liftFromPolyCompletion_unique p _ hc g rfl).symm

private def restrictSmall {Q' : Poly C} {m n : ℕ}
    (g : (D m).carrier →ₐ[C]
      (term p γC hp' (PDPolynomialFunctor.base_ker (J := I) Q')
        (PDPolynomialFunctor.frame (J := I) Q') n).carrier) :
    (D m).carrier →ₐ[W]
      (term p γC hp' (PDPolynomialFunctor.base_ker (J := I) Q')
        (PDPolynomialFunctor.frame (J := I) Q') n).carrier :=
  ⟨g.toRingHom, fun x => g.commutes (wZero p C x)⟩

private theorem eval_mapCopies {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) (i : Fin (m + 1)) :
    (mapCopies p γC hp' hI small θ).toRingHom.comp (eval P hpC hlocal Q m i) =
      eval P hpC hlocal Q n (θ i) := by
  apply fromCompletion_ext P Q (D n).isEnvelope.complete
  apply RingHom.ext
  intro x
  change mapCopies p γC hp' hI small θ
    (eval P hpC hlocal Q m i (prismPolynomialUnit P (Fin Q.n) x)) =
    eval P hpC hlocal Q n (θ i) (prismPolynomialUnit P (Fin Q.n) x)
  simp only [eval_unit]
  exact DFunLike.congr_fun (PDPolynomialFunctor.mapCopies_copyEval p γC hp' Q θ i) x

private theorem mapAt_mapCopies {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) :
    (mapAt P hpC hlocal Q n).comp (mapCopies p γW hpW hJ large θ) =
      (restrictSmall P hpC hlocal Q (mapCopies p γC hp' hI small θ)).comp
        (mapAt P hpC hlocal Q m) := by
  apply hom_ext p γW hpW hJ large (D n).isEnvelope.complete
    ((mapAt_isDPMorphism P hpC hlocal Q n).comp _ (mapCopies_isDPMorphism p γW hpW hJ large θ))
    ((mapCopies_isDPMorphism p γC hp' hI small θ).comp _
      (mapAt_isDPMorphism P hpC hlocal Q m))
  intro x
  simp only [AlgHom.comp_apply, mapCopies_variableImage, mapAt_X]
  exact (RingHom.congr_fun (eval_mapCopies P hpC hlocal Q θ x.2) x.1).symm

local notation "resW" => Under.map (CommRingCat.ofHom (wZero p C))

private def finiteFrame (Q : Poly C) :
    (wittBigPdModel P hpC hlocal).obj Q ⟶
      (PDPolynomialFunctor.nerve p γC hp').obj Q ⋙ resW where
  app n := underMap (mapAt P hpC hlocal Q n.len)
  naturality {m n} θ := by
    apply Under.UnderMorphism.ext
    exact congrArg (fun g => CommRingCat.ofHom (AlgHom.toRingHom g))
      (mapAt_mapCopies P hpC hlocal Q θ.toOrderHom)

section Substitution

variable {Q₁ Q' : Poly (A ⧸ P.ideal)} (f : Q₁ ⟶ Q')

local notation "large₁" => (Ideal.Quotient.mk (Ideal.span {(p : polyCompletion P Q₁.n)}))
local notation "hJ₁" => wittBaseKer P Q₁

local notation "small'" => PDPolynomialFunctor.frame (J := I) Q'
local notation "large'" => (Ideal.Quotient.mk (Ideal.span {(p : polyCompletion P Q'.n)}))
local notation "D'" => term p γC hp' (PDPolynomialFunctor.base_ker (J := I) Q') small'
local notation "rmap" => bigResidueMap (k := W) P f

private theorem eval_mapAt (n : ℕ) (i : Fin (n + 1)) :
    (PDPolynomialFunctor.mapAt p γC hp' f n).toRingHom.comp (eval P hpC hlocal Q₁ n i) =
      (eval P hpC hlocal Q' n i).comp (polyCompletionMap P f).toRingHom := by
  apply fromCompletion_ext P Q₁ (D' n).isEnvelope.complete
  apply RingHom.ext
  intro x
  change PDPolynomialFunctor.mapAt p γC hp' f n
    (eval P hpC hlocal Q₁ n i (prismPolynomialUnit P (Fin Q₁.n) x)) =
    eval P hpC hlocal Q' n i
      (polyCompletionMap P f (prismPolynomialUnit P (Fin Q₁.n) x))
  simp only [polyCompletionMap_unit, eval_unit]
  exact DFunLike.congr_fun (PDPolynomialFunctor.mapAt_copyEval p γC hp' f i) x

private theorem mapAt_rename (n : ℕ) :
    (mapAt P hpC hlocal Q' n).comp (renameAt p γW hpW hJ₁ (wittBaseKer P Q')
      large₁ large' rmap (polyCompletionMap P f) (fun x => (bigResidueMap_mk P f x).symm) n) =
      (restrictSmall P hpC hlocal Q₁ (PDPolynomialFunctor.mapAt p γC hp' f n)).comp
        (mapAt P hpC hlocal Q₁ n) := by
  apply hom_ext p γW hpW hJ₁ large₁ (D' n).isEnvelope.complete
    ((mapAt_isDPMorphism P hpC hlocal Q' n).comp _ (renameAt_isDPMorphism ..))
    ((PDPolynomialFunctor.mapAt_isDPMorphism p γC hp' f n).comp _
      (mapAt_isDPMorphism P hpC hlocal Q₁ n))
  intro x
  simp only [AlgHom.comp_apply, renameAt_variableImage, mapAt_X]
  exact (RingHom.congr_fun (eval_mapAt P hpC hlocal f n x.2) x.1).symm

end Substitution

private def toFinite :
    wittBigPdModel P hpC hlocal ⟶
      PDPolynomialFunctor.nerve p γC hp' ⋙ (Functor.whiskeringRight _ _ _).obj resW where
  app Q := finiteFrame P hpC hlocal Q
  naturality {Q Q'} f := by
    apply NatTrans.ext
    funext n
    apply Under.UnderMorphism.ext
    exact congrArg (fun g => CommRingCat.ofHom (AlgHom.toRingHom g))
      (mapAt_rename P hpC hlocal f n.len)

variable (hk : IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal))

/-- 第 0 Witt 成分に沿って小さい分冪模型へ送る厳密な自然変換。 -/
def _root_.SerrePositivity.BhattScholze.Prismatic.wittToSmall :
    wittBigPdModel P hpC hlocal ⟶
      pdPolynomialFunctor p γC (Ideal.mem_span_singleton_self (p : C)) hk hpC ⋙
      (Functor.whiskeringRight _ _ _).obj resW :=
  toFinite P hpC hlocal ≫ Functor.whiskerRight
    (PDPolynomialFunctor.smallIsoNatural p γC hp' hk hpC).inv
    ((Functor.whiskeringRight _ _ _).obj resW)

end SerrePositivity.BhattScholze.Prismatic.WittToSmall
