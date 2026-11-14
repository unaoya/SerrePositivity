module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# 剰余環と変数の写像に沿う分冪 Čech 脈体

## 概要
剰余環の代数射と、それに両立する枠の変数の写像は完備分冪包の余単体写像を誘導する。

## 方針
多項式の改名が評価の核を保つことを確認し、分冪包の普遍性を適用する。
恒等・合成と頂点写像との交換は、変数の像で示す。

## 規約
基底の分冪環を固定する。剰余環は写像に沿って変えてよい。

## 使われ方
BS 著者版 Theorem 6.4 の大きい分冪模型を多項式代数について厳密に関手化する。
-/

public noncomputable section

open CategoryTheory

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PDCechNerve

variable {k A A' A'' : Type u} [CommRing k] [CommRing A] [CommRing A'] [CommRing A'']
variable [Algebra k A] [Algebra k A'] [Algebra k A'']
variable (p : ℕ) {J : Ideal k} (γ : DividedPowers J) (hp : (p : k) ∈ J)
variable (hJ : J ≤ RingHom.ker (algebraMap k A))
variable (hJ' : J ≤ RingHom.ker (algebraMap k A'))
variable (hJ'' : J ≤ RingHom.ker (algebraMap k A''))
variable {S S' S'' : Type u} (s : S → A) (s' : S' → A') (s'' : S'' → A'')
variable (f : A →ₐ[k] A') (σ : S → S') (hσ : ∀ x, s' (σ x) = f (s x))

local notation "D" => term p γ hp hJ
local notation "D'" => term p γ hp hJ'
local notation "D''" => term p γ hp hJ''

private def renameFrame (n : ℕ) : pdFrame k S n →ₐ[k] pdFrame k S' n :=
  MvPolynomial.rename (fun x => (σ x.1, x.2))

include hσ in
private theorem renameFrame_ker (n : ℕ) :
    (RingHom.ker (pdFrameEval (k := k) s n)).map (renameFrame (k := k) σ n) ≤
      RingHom.ker (pdFrameEval (k := k) s' n) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  have he : (pdFrameEval (k := k) s' n).comp (renameFrame (k := k) σ n) =
      f.comp (pdFrameEval (k := k) s n) := by
    apply MvPolynomial.algHom_ext
    intro x
    simp [renameFrame, hσ]
  change pdFrameEval (k := k) s' n (renameFrame σ n a) = 0
  rw [show pdFrameEval (k := k) s' n (renameFrame σ n a) = f (pdFrameEval (k := k) s n a)
      from DFunLike.congr_fun he a, RingHom.mem_ker.mp ha, map_zero]

include hσ in
private theorem renameUnit_map_le (n : ℕ) :
    (RingHom.ker (pdFrameEval (k := k) s n)).map ((D' s' n).unit.comp (renameFrame σ n)) ≤
      (D' s' n).ideal := by
  change Ideal.map ((D' s' n).unit.toRingHom.comp (renameFrame σ n).toRingHom) _ ≤ _
  rw [← Ideal.map_map]
  exact (Ideal.map_mono (renameFrame_ker s s' f σ hσ n)).trans (D' s' n).isEnvelope.map_le

/-- 剰余の評価と可換な変数の改名を分冪包へ延長する。 -/
def renameAt (n : ℕ) : (D s n).carrier →ₐ[k] (D' s' n).carrier :=
  (D s n).isEnvelope.liftHom (D' s' n).isEnvelope.complete
    ((D' s' n).unit.comp (renameFrame σ n))
    (renameUnit_map_le p γ hp hJ' s s' f σ hσ n)
    (D' s' n).isEnvelope.base_dp

/-- 改名の延長は分冪を保つ。 -/
theorem renameAt_isDPMorphism (n : ℕ) :
    (D s n).dividedPowers.IsDPMorphism (D' s' n).dividedPowers
      (renameAt p γ hp hJ hJ' s s' f σ hσ n).toRingHom :=
  (D s n).isEnvelope.liftHom_isDPMorphism ..

/-- 改名の延長は指定した変数の写像を実現する。 -/
@[simp] theorem renameAt_variableImage (n : ℕ) (x : S × Fin (n + 1)) :
    renameAt p γ hp hJ hJ' s s' f σ hσ n (variableImage p γ hp hJ s n x) =
      variableImage p γ hp hJ' s' n (σ x.1, x.2) := by
  have hc : (renameAt p γ hp hJ hJ' s s' f σ hσ n).comp (D s n).unit =
      (D' s' n).unit.comp (renameFrame σ n) :=
    (D s n).isEnvelope.liftHom_comp (D' s' n).isEnvelope.complete _
      (renameUnit_map_le p γ hp hJ' s s' f σ hσ n) (D' s' n).isEnvelope.base_dp
  have h := DFunLike.congr_fun hc (MvPolynomial.X x)
  change renameAt p γ hp hJ hJ' s s' f σ hσ n (variableImage p γ hp hJ s n x) =
    (D' s' n).unit (MvPolynomial.X (σ x.1, x.2))
  exact h.trans (congrArg (D' s' n).unit (MvPolynomial.rename_X _ _))

private theorem renameAt_naturality {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) :
    (renameAt p γ hp hJ hJ' s s' f σ hσ n).comp (mapCopies p γ hp hJ s θ) =
      (mapCopies p γ hp hJ' s' θ).comp (renameAt p γ hp hJ hJ' s s' f σ hσ m) := by
  apply hom_ext p γ hp hJ s (D' s' n).isEnvelope.complete
    ((renameAt_isDPMorphism p γ hp hJ hJ' s s' f σ hσ n).comp _
      (mapCopies_isDPMorphism p γ hp hJ s θ))
    ((mapCopies_isDPMorphism p γ hp hJ' s' θ).comp _
      (renameAt_isDPMorphism p γ hp hJ hJ' s s' f σ hσ m))
  intro x
  simp

/-- 評価と両立する変数の改名は余単体的代数の射を誘導する。 -/
@[expose] def rename :
    pdCechNerve p γ hp hJ s ⟶ pdCechNerve p γ hp hJ' s' where
  app n := underMap (renameAt p γ hp hJ hJ' s s' f σ hσ n.len)
  naturality {m n} θ := by
    apply Under.UnderMorphism.ext
    exact congrArg (fun a => CommRingCat.ofHom (AlgHom.toRingHom a))
      (renameAt_naturality p γ hp hJ hJ' s s' f σ hσ θ.toOrderHom)

/-- 剰余環と変数への写像が等しいとき、誘導される脈体の写像は一致する。 -/
theorem rename_congr {g : A →ₐ[k] A'} {τ : S → S'}
    {hτ : ∀ x, s' (τ x) = g (s x)} (hf : f = g) (hσ' : σ = τ) :
    rename p γ hp hJ hJ' s s' f σ hσ = rename p γ hp hJ hJ' s s' g τ hτ := by
  subst g
  subst τ
  rfl

/-- 恒等改名は余単体的代数の恒等射を与える。 -/
@[simp] theorem rename_id :
    rename p γ hp hJ hJ s s (AlgHom.id k A) id (fun _ => rfl) =
      𝟙 (pdCechNerve p γ hp hJ s) := by
  apply NatTrans.ext
  funext n
  have h : renameAt p γ hp hJ hJ s s (AlgHom.id k A) id (fun _ => rfl) n.len =
      AlgHom.id k (D s n.len).carrier := by
    apply hom_ext p γ hp hJ s (D s n.len).isEnvelope.complete
      (renameAt_isDPMorphism p γ hp hJ hJ s s _ _ _ _)
      (DividedPowers.DPMorphism.id (D s n.len).dividedPowers).isDPMorphism
    rintro ⟨x, i⟩
    exact renameAt_variableImage p γ hp hJ hJ s s (AlgHom.id k A) id _ n.len (x, i)
  exact congrArg underMap h

/-- 二つの改名の合成は変数の写像の合成で与えられる。 -/
theorem rename_comp (g : A' →ₐ[k] A'') (τ : S' → S'') (hτ : ∀ x, s'' (τ x) = g (s' x)) :
    rename p γ hp hJ hJ' s s' f σ hσ ≫ rename p γ hp hJ' hJ'' s' s'' g τ hτ =
      rename p γ hp hJ hJ'' s s'' (g.comp f) (τ ∘ σ)
        (fun x => (hτ (σ x)).trans (congrArg g (hσ x))) := by
  apply NatTrans.ext
  funext n
  have he : ∀ x, s'' ((τ ∘ σ) x) = (g.comp f) (s x) := fun x =>
    (hτ (σ x)).trans (congrArg g (hσ x))
  have h : (renameAt p γ hp hJ' hJ'' s' s'' g τ hτ n.len).comp
        (renameAt p γ hp hJ hJ' s s' f σ hσ n.len) =
      renameAt p γ hp hJ hJ'' s s'' (g.comp f) (τ ∘ σ) he n.len := by
    apply hom_ext p γ hp hJ s (D'' s'' n.len).isEnvelope.complete
      ((renameAt_isDPMorphism p γ hp hJ' hJ'' s' s'' g τ hτ n.len).comp _
        (renameAt_isDPMorphism p γ hp hJ hJ' s s' f σ hσ n.len))
      (renameAt_isDPMorphism p γ hp hJ hJ'' s s'' (g.comp f) (τ ∘ σ) he n.len)
    intro x
    simp
  exact congrArg underMap h

end SerrePositivity.BhattScholze.Prismatic.PDCechNerve
