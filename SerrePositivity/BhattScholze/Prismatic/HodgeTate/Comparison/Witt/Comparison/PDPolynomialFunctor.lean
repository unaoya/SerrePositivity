module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.PolynomialCategory
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve

/-!
# 小さい分冪 Čech 模型の多項式代入

## 概要
多項式代数の準同型を、頂点ごとの代入により小さい完備分冪模型へ延長する。

## 方針
各頂点で多項式を評価し、剰余の評価核を保つことを確かめて完備分冪包の普遍性を使う。
恒等・合成は各頂点の変数上で確かめる。

## 規約
係数の分冪イデアルを固定する。剰余多項式の係数にはそのイデアルによる商を使う。

## 使われ方
BS 著者版 Theorem 6.4 の小さい分冪模型の厳密な関手性。
-/

public noncomputable section

open CategoryTheory

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PDPolynomialFunctor

open PDCechNerve

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [CommRing k] (p : ℕ) {J : Ideal k} (γ : DividedPowers J)
variable (hp : (p : k) ∈ J)

private abbrev residue (Q : Poly k) := MvPolynomial (Fin Q.n) (k ⧸ J)

private theorem base_ker (Q : Poly k) : J ≤ RingHom.ker (algebraMap k (residue (J := J) Q)) := by
  intro x hx
  change MvPolynomial.C (Ideal.Quotient.mk J x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

private def frame (Q : Poly k) : ULift.{u} (Fin Q.n) → residue (J := J) Q :=
  fun j => MvPolynomial.X j.down

local notation "D" => fun Q n => term p γ hp (base_ker Q) (frame Q) n
local notation "V" => fun Q n => variableImage p γ hp (base_ker Q) (frame Q) n

private def copyEval (Q : Poly k) {n : ℕ} (i : Fin (n + 1)) :
    MvPolynomial (Fin Q.n) k →ₐ[k] (D Q n).carrier :=
  MvPolynomial.aeval (fun j => V Q n (ULift.up j, i))

private theorem augmentation_copyEval (Q : Poly k) {n : ℕ} (i : Fin (n + 1)) :
    (augmentation p γ hp (base_ker Q) (frame Q) n).comp (copyEval p γ hp Q i) =
      MvPolynomial.mapAlgHom (Ideal.Quotient.mkₐ k J) := by
  apply MvPolynomial.algHom_ext
  intro j
  change augmentation p γ hp (base_ker Q) (frame Q) n
    (MvPolynomial.aeval (fun j => V Q n (ULift.up j, i)) (MvPolynomial.X j)) = _
  rw [MvPolynomial.aeval_X, augmentation_variableImage]
  exact (MvPolynomial.map_X _ _).symm

private theorem mapCopies_copyEval (Q : Poly k) {m n : ℕ}
    (θ : Fin (m + 1) → Fin (n + 1)) (i : Fin (m + 1)) :
    (mapCopies p γ hp (base_ker Q) (frame Q) θ).comp (copyEval p γ hp Q i) =
      copyEval p γ hp Q (θ i) := by
  apply MvPolynomial.algHom_ext
  intro j
  change mapCopies p γ hp (base_ker Q) (frame Q) θ
    (MvPolynomial.aeval (fun j => V Q m (ULift.up j, i)) (MvPolynomial.X j)) =
    MvPolynomial.aeval (fun j => V Q n (ULift.up j, θ i)) (MvPolynomial.X j)
  rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X, mapCopies_variableImage]

variable {Q Q' Q'' : Poly k} (f : Q ⟶ Q')

private def substitution (n : ℕ) : pdFrame k (ULift.{u} (Fin Q.n)) n →ₐ[k] (D Q' n).carrier :=
  MvPolynomial.aeval (fun x => copyEval p γ hp Q' x.2 (Poly.hom f (MvPolynomial.X x.1.down)))

set_option maxHeartbeats 600000 in
-- 分冪包の標準脚を剰余環の係数と照合する。
private theorem substitution_ker (n : ℕ) :
    (RingHom.ker (pdFrameEval (k := k) (frame (J := J) Q) n)).map
      (substitution p γ hp f n) ≤ (D Q' n).ideal := by
  rw [Ideal.map_le_iff_le_comap, ← augmentation_ker p γ hp (base_ker Q') (frame Q') n]
  have h : (augmentation p γ hp (base_ker Q') (frame Q') n).comp
      (substitution p γ hp f n) =
    ((changePolyHom (Ideal.Quotient.mk J) f).restrictScalars k).comp
      (pdFrameEval (k := k) (frame Q) n) := by
    apply MvPolynomial.algHom_ext
    intro x
    change augmentation p γ hp (base_ker Q') (frame Q') n
      (substitution p γ hp f n (MvPolynomial.X x)) =
      changePolyHom (Ideal.Quotient.mk J) f (pdFrameEval (k := k) (frame Q) n (MvPolynomial.X x))
    rw [substitution, MvPolynomial.aeval_X, pdFrameEval_X]
    change _ = changePolyHom (Ideal.Quotient.mk J) f (MvPolynomial.X x.1.down)
    unfold changePolyHom
    rw [MvPolynomial.aeval_X]
    exact DFunLike.congr_fun (augmentation_copyEval p γ hp Q' x.2)
      (Poly.hom f (MvPolynomial.X x.1.down))
  let aug := augmentation p γ hp (base_ker Q') (frame Q') n
  let sub := substitution p γ hp f n
  let ev := pdFrameEval (k := k) (frame (J := J) Q) n
  let g := (changePolyHom (Ideal.Quotient.mk J) f).restrictScalars k
  change aug.comp sub = g.comp ev at h
  change RingHom.ker ev ≤ (RingHom.ker aug).comap sub
  intro x hx
  have hx' : ev x = 0 := RingHom.mem_ker.mp hx
  change aug (sub x) = 0
  calc
    aug (sub x) = g (ev x) := DFunLike.congr_fun h x
    _ = 0 := by rw [hx', map_zero]

/-- 多項式代入の各次数の延長。 -/
private def mapAt (n : ℕ) : (D Q n).carrier →ₐ[k] (D Q' n).carrier :=
  (D Q n).isEnvelope.liftHom (D Q' n).isEnvelope.complete (substitution p γ hp f n)
    (substitution_ker p γ hp f n) (D Q' n).isEnvelope.base_dp

private theorem mapAt_isDPMorphism (n : ℕ) :
    (D Q n).dividedPowers.IsDPMorphism (D Q' n).dividedPowers (mapAt p γ hp f n).toRingHom :=
  (D Q n).isEnvelope.liftHom_isDPMorphism ..

private theorem mapAt_X (n : ℕ) (x : ULift.{u} (Fin Q.n) × Fin (n + 1)) :
    mapAt p γ hp f n (V Q n x) =
      copyEval p γ hp Q' x.2 (Poly.hom f (MvPolynomial.X x.1.down)) := by
  have h : (mapAt p γ hp f n).comp (D Q n).unit = substitution p γ hp f n :=
    (D Q n).isEnvelope.liftHom_comp ..
  exact (DFunLike.congr_fun h (MvPolynomial.X x)).trans (MvPolynomial.aeval_X _ _)

private theorem mapAt_copyEval {n : ℕ} (i : Fin (n + 1)) :
    (mapAt p γ hp f n).comp (copyEval p γ hp Q i) =
      (copyEval p γ hp Q' i).comp (Poly.hom f) := by
  apply MvPolynomial.algHom_ext
  intro j
  change mapAt p γ hp f n (copyEval p γ hp Q i (MvPolynomial.X j)) =
    copyEval p γ hp Q' i (Poly.hom f (MvPolynomial.X j))
  rw [copyEval, MvPolynomial.aeval_X]
  exact mapAt_X p γ hp f n (ULift.up j, i)

private theorem mapAt_naturality {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) :
    (mapAt p γ hp f n).comp (mapCopies p γ hp (base_ker Q) (frame Q) θ) =
      (mapCopies p γ hp (base_ker Q') (frame Q') θ).comp (mapAt p γ hp f m) := by
  apply hom_ext p γ hp (base_ker Q) (frame Q) (D Q' n).isEnvelope.complete
    ((mapAt_isDPMorphism p γ hp f n).comp _
      (mapCopies_isDPMorphism p γ hp (base_ker Q) (frame Q) θ))
    ((mapCopies_isDPMorphism p γ hp (base_ker Q') (frame Q') θ).comp _
      (mapAt_isDPMorphism p γ hp f m))
  intro x
  simp only [AlgHom.comp_apply, mapCopies_variableImage, mapAt_X]
  exact (DFunLike.congr_fun (mapCopies_copyEval p γ hp Q' θ x.2)
    (Poly.hom f (MvPolynomial.X x.1.down))).symm

private theorem mapAt_id (Q : Poly k) (n : ℕ) : mapAt p γ hp (𝟙 Q) n = AlgHom.id k _ := by
  apply hom_ext p γ hp (base_ker Q) (frame Q) (D Q n).isEnvelope.complete
    (mapAt_isDPMorphism p γ hp (𝟙 Q) n)
    (DividedPowers.DPMorphism.id (D Q n).dividedPowers).isDPMorphism
  rintro ⟨⟨j⟩, i⟩
  rw [mapAt_X]
  change copyEval p γ hp Q i (MvPolynomial.X j) = V Q n (ULift.up j, i)
  exact MvPolynomial.aeval_X _ _

private theorem mapAt_comp (g : Q' ⟶ Q'') (n : ℕ) :
    mapAt p γ hp (f ≫ g) n = (mapAt p γ hp g n).comp (mapAt p γ hp f n) := by
  apply hom_ext p γ hp (base_ker Q) (frame Q) (D Q'' n).isEnvelope.complete
    (mapAt_isDPMorphism p γ hp (f ≫ g) n)
    ((mapAt_isDPMorphism p γ hp g n).comp _ (mapAt_isDPMorphism p γ hp f n))
  intro x
  simp only [AlgHom.comp_apply, mapAt_X]
  exact (DFunLike.congr_fun (mapAt_copyEval p γ hp g x.2)
    (Poly.hom f (MvPolynomial.X x.1.down))).symm

/-- 有限枠の分冪 Čech 脈体は多項式代入について厳密に関手的。 -/
def nerve :
    Poly k ⥤ SimplexCategory ⥤ Under (CommRingCat.of k) where
  obj Q := pdCechNerve p γ hp (base_ker Q) (frame Q)
  map f :=
    { app n := underMap (mapAt p γ hp f n.len)
      naturality {m n} θ := by
        apply Under.UnderMorphism.ext
        exact congrArg (fun a => CommRingCat.ofHom (AlgHom.toRingHom a))
          (mapAt_naturality p γ hp f θ.toOrderHom) }
  map_id Q := by
    apply NatTrans.ext
    funext n
    exact congrArg underMap (mapAt_id p γ hp Q n.len)
  map_comp f g := by
    apply NatTrans.ext
    funext n
    exact congrArg underMap (mapAt_comp p γ hp f g n.len)

section Small

variable [Fact p.Prime]
variable (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
variable (hreg : Function.Injective (fun x : k => (p : k) * x))

private def smallIso (Q : Poly k) : pdModel p k Q.n ≅ (nerve p γ hp).obj Q :=
  pdModel_iso_pdCechNerve p k γ hp
    (fun _ => γ.factorial_mul_dpow_eq_pow hp) hk hreg Q.n (base_ker Q)

/-- 小さい模型の各値を分冪 Čech 脈体と照合し、多項式代入を移す。 -/
def _root_.SerrePositivity.BhattScholze.Prismatic.pdPolynomialFunctor :
    Poly k ⥤ SimplexCategory ⥤ Under (CommRingCat.of k) where
  obj Q := pdModel p k Q.n
  map {Q Q'} f := (smallIso p γ hp hk hreg Q).hom ≫ (nerve p γ hp).map f ≫
    (smallIso p γ hp hk hreg Q').inv
  map_id Q := by simp
  map_comp f g := by simp

/-- 小さい模型と有限枠との照合は多項式代入に関して自然。 -/
def smallIsoNatural : pdPolynomialFunctor p γ hp hk hreg ≅ nerve p γ hp :=
  NatIso.ofComponents (smallIso p γ hp hk hreg) fun _ => by
    dsimp only [pdPolynomialFunctor]
    simp

end Small

end SerrePositivity.BhattScholze.Prismatic.PDPolynomialFunctor
