module

public import SerrePositivity.CommutativeAlgebra.DividedPowers.Envelopes.CompletedPDEnvelope
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# 枠の p 完備分冪 Čech 脈体

## 概要
枠の各頂点に変数を置き、剰余環への評価の核の相対分冪包を取る。
BS 著者版 Theorem 5.2、Stacks 07HP の affine 模型。

## 方針
変数の像を指定し、完備分冪包の普遍性で延長する。
余単体恒等式、増大との両立は分冪を保つ延長の一意性から従う。

## 規約
頂点は `Fin (n+1)`。基底の分冪イデアルの像は剰余環で零。

## 使われ方
枠の取り替え、小さい分冪模型との比較、結晶サイトの塔。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency true

open CategoryTheory
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

/-- 枠の `n+1` 個の頂点の多項式環。 -/
abbrev pdFrame (k : Type u) [CommRing k] (S : Type u) (n : ℕ) :=
  MvPolynomial (S × Fin (n + 1)) k

/-- すべての頂点の変数を指定した剰余環の元で評価する。 -/
def pdFrameEval {k : Type u} [CommRing k] {A : Type u} [CommRing A] [Algebra k A]
    {S : Type u} (s : S → A) (n : ℕ) : pdFrame k S n →ₐ[k] A :=
  MvPolynomial.aeval fun x => s x.1

@[simp]
theorem pdFrameEval_X {k : Type u} [CommRing k] {A : Type u} [CommRing A] [Algebra k A]
    {S : Type u} (s : S → A) (n : ℕ) (x : S × Fin (n + 1)) :
    pdFrameEval (k := k) s n (MvPolynomial.X x) = s x.1 :=
  MvPolynomial.aeval_X _ _

namespace PDCechNerve

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
variable (p : ℕ) {J : Ideal k} (γ : DividedPowers J) (hp : (p : k) ∈ J)
variable (hJ : J ≤ RingHom.ker (algebraMap k A))
variable {S S' : Type u} (s : S → A) (s' : S' → A)

include hJ in
private theorem base_le_ker (n : ℕ) :
    J.map (algebraMap k (pdFrame k S n)) ≤ RingHom.ker (pdFrameEval (k := k) s n) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change pdFrameEval (k := k) s n (algebraMap k (pdFrame k S n) x) = 0
  rw [AlgHom.commutes]
  exact hJ hx

/-- 各次数の枠の評価の核の p 完備分冪包。 -/
@[irreducible] def term (n : ℕ) :
    CompletedPDEnvelopeData p γ (RingHom.ker (pdFrameEval (k := k) s n)) :=
  completedPDEnvelope p γ hp _ (base_le_ker hJ s n)

local notation "D" => term p γ hp hJ

include hp hJ in
private theorem complete_target : IsAdicComplete (Ideal.span {(p : A)}) A := by
  have hz : (p : A) = 0 := by simpa only [map_natCast] using RingHom.mem_ker.mp (hJ hp)
  exact isAdicComplete_of_natCast_zero hz

/-- 各次数の分冪包から剰余環への評価。 -/
def augmentation (n : ℕ) : (D s n).carrier →ₐ[k] A :=
  (D s n).isEnvelope.liftHom (ε := dividedPowersBot A) (complete_target p hp hJ)
    (pdFrameEval (k := k) s n) (Ideal.map_le_iff_le_comap.mpr le_rfl)
    (isDPMorphismToBot γ _ hJ)

@[simp]
theorem augmentation_unit (n : ℕ) (x : pdFrame k S n) :
    augmentation p γ hp hJ s n ((D s n).unit x) = pdFrameEval (k := k) s n x :=
  DFunLike.congr_fun ((D s n).isEnvelope.liftHom_comp ..) x

theorem augmentation_isDPMorphism (n : ℕ) :
    (D s n).dividedPowers.IsDPMorphism (dividedPowersBot A)
      (augmentation p γ hp hJ s n).toRingHom :=
  (D s n).isEnvelope.liftHom_isDPMorphism ..

private theorem augmentation_ker (n : ℕ) :
    RingHom.ker (augmentation p γ hp hJ s n).toRingHom = (D s n).ideal := by
  let e := (D s n).isEnvelope.quotientEquiv hp (base_le_ker hJ s n)
  let q := Ideal.Quotient.mkₐ k (D s n).ideal
  let f := (Ideal.kerLiftAlg (pdFrameEval (k := k) s n)).comp (e.toAlgHom.comp q)
  have hf : f = augmentation p γ hp hJ s n := by
    apply (D s n).isEnvelope.hom_ext (complete_target p hp hJ)
      (isDPMorphismToBot (D s n).dividedPowers f.toRingHom (fun x hx => by
        change (Ideal.kerLiftAlg (pdFrameEval (k := k) s n)) (e (q x)) = 0
        rw [show q x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero, map_zero]))
      (augmentation_isDPMorphism p γ hp hJ s n)
    apply AlgHom.ext
    intro x
    change (Ideal.kerLiftAlg (pdFrameEval (k := k) s n))
      (e (Ideal.Quotient.mk _ ((D s n).unit x))) = _
    rw [IsCompletedPDEnvelope.quotientEquiv_mk_unit, Ideal.kerLiftAlg_mk]
    exact (augmentation_unit p γ hp hJ s n x).symm
  rw [← hf]
  ext x
  change (Ideal.kerLiftAlg (pdFrameEval (k := k) s n)) (e (q x)) = 0 ↔ x ∈ (D s n).ideal
  rw [map_eq_zero_iff _ (Ideal.kerLiftAlg_injective _), map_eq_zero_iff _ e.injective]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- 頂点に置いた変数の標準像。 -/
def variableImage (n : ℕ) (x : S × Fin (n + 1)) : (D s n).carrier :=
  (D s n).unit (MvPolynomial.X x)

@[simp]
theorem augmentation_variableImage (n : ℕ) (x : S × Fin (n + 1)) :
    augmentation p γ hp hJ s n (variableImage p γ hp hJ s n x) = s x.1 := by
  simp [variableImage]

/-- 変数の像で分冪包からの射を定める。 -/
def mapVariables {m n : ℕ} (f : S × Fin (m + 1) → (D s' n).carrier)
    (hf : ∀ x, augmentation p γ hp hJ s' n (f x) = s x.1) :
    (D s m).carrier →ₐ[k] (D s' n).carrier :=
  (D s m).isEnvelope.liftHom (D s' n).isEnvelope.complete (MvPolynomial.aeval f)
    (by
      rw [Ideal.map_le_iff_le_comap, ← augmentation_ker p γ hp hJ s' n]
      have he : (augmentation p γ hp hJ s' n).comp (MvPolynomial.aeval f) =
          pdFrameEval (k := k) s m := by
        apply MvPolynomial.algHom_ext
        simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X, pdFrameEval_X] using hf
      intro x hx
      exact (DFunLike.congr_fun he x).trans hx)
    (D s' n).isEnvelope.base_dp

/-- 指定した変数像からの延長は分冪を保つ。 -/
theorem mapVariables_isDPMorphism {m n : ℕ} (f : S × Fin (m + 1) → (D s' n).carrier)
    (hf : ∀ x, augmentation p γ hp hJ s' n (f x) = s x.1) :
    (D s m).dividedPowers.IsDPMorphism (D s' n).dividedPowers
      (mapVariables p γ hp hJ s s' f hf).toRingHom :=
  (D s m).isEnvelope.liftHom_isDPMorphism ..

@[simp]
theorem mapVariables_variableImage {m n : ℕ} (f : S × Fin (m + 1) → (D s' n).carrier)
    (hf : ∀ x, augmentation p γ hp hJ s' n (f x) = s x.1) (x : S × Fin (m + 1)) :
    mapVariables p γ hp hJ s s' f hf (variableImage p γ hp hJ s m x) = f x :=
  (DFunLike.congr_fun ((D s m).isEnvelope.liftHom_comp ..) (MvPolynomial.X x)).trans
    (MvPolynomial.aeval_X _ _)

/-- 枠の分冪包からの分冪射の等しさは変数上で確かめればよい。 -/
theorem hom_ext {m : ℕ} {E : Type u} [CommRing E] [Algebra k E]
    {L : Ideal E} {ε : DividedPowers L} (hE : IsAdicComplete (Ideal.span {(p : E)}) E)
    {f g : (D s m).carrier →ₐ[k] E}
    (hf : (D s m).dividedPowers.IsDPMorphism ε f.toRingHom)
    (hg : (D s m).dividedPowers.IsDPMorphism ε g.toRingHom)
    (he : ∀ x, f (variableImage p γ hp hJ s m x) = g (variableImage p γ hp hJ s m x)) :
    f = g :=
  (D s m).isEnvelope.hom_ext hE hf hg (MvPolynomial.algHom_ext he)

/-- 頂点の写像は各頂点の変数をその像へ送る。 -/
def mapCopies {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    (D s m).carrier →ₐ[k] (D s n).carrier :=
  mapVariables p γ hp hJ s s (m := m) (n := n)
    (fun x => variableImage p γ hp hJ s n (x.1, f x.2)) (fun x => by simp)

@[simp]
theorem mapCopies_variableImage {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (x : S × Fin (m + 1)) :
    mapCopies p γ hp hJ s f (variableImage p γ hp hJ s m x) =
      variableImage p γ hp hJ s n (x.1, f x.2) :=
  mapVariables_variableImage ..

theorem mapCopies_isDPMorphism {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    (D s m).dividedPowers.IsDPMorphism (D s n).dividedPowers
      (mapCopies p γ hp hJ s f).toRingHom :=
  mapVariables_isDPMorphism ..

@[simp]
theorem augmentation_mapCopies {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (x : (D s m).carrier) :
    augmentation p γ hp hJ s n (mapCopies p γ hp hJ s f x) = augmentation p γ hp hJ s m x := by
  have he : (augmentation p γ hp hJ s n).comp (mapCopies p γ hp hJ s f) =
      augmentation p γ hp hJ s m := by
    apply hom_ext p γ hp hJ s (complete_target p hp hJ)
      ((augmentation_isDPMorphism p γ hp hJ s n).comp _ (mapCopies_isDPMorphism p γ hp hJ s f))
      (augmentation_isDPMorphism p γ hp hJ s m)
    intro y
    simp
  exact DFunLike.congr_fun he x

theorem mapCopies_id (n : ℕ) : mapCopies p γ hp hJ s (id : Fin (n + 1) → _) = AlgHom.id k _ := by
  apply hom_ext p γ hp hJ s (D s n).isEnvelope.complete
    (mapCopies_isDPMorphism p γ hp hJ s _)
    (DividedPowers.DPMorphism.id (D s n).dividedPowers).isDPMorphism
  intro x
  cases x
  simp

theorem mapCopies_comp {m n l : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (g : Fin (n + 1) → Fin (l + 1)) :
    mapCopies p γ hp hJ s (g ∘ f) =
      (mapCopies p γ hp hJ s g).comp (mapCopies p γ hp hJ s f) := by
  apply hom_ext p γ hp hJ s (D s l).isEnvelope.complete
    (mapCopies_isDPMorphism p γ hp hJ s _)
    ((mapCopies_isDPMorphism p γ hp hJ s g).comp _ (mapCopies_isDPMorphism p γ hp hJ s f))
  intro x
  simp

@[simp]
theorem mapCopies_mapCopies {m n l : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (g : Fin (n + 1) → Fin (l + 1)) (x : (D s m).carrier) :
    mapCopies p γ hp hJ s g (mapCopies p γ hp hJ s f x) =
      mapCopies p γ hp hJ s (g ∘ f) x :=
  (DFunLike.congr_fun (mapCopies_comp p γ hp hJ s f g) x).symm

/-- 基底の下の圏で代数射を読む。 -/
@[expose] def underMap {B E : Type u} [CommRing B] [CommRing E] [Algebra k B] [Algebra k E]
    (f : B →ₐ[k] E) :
    Under.mk (CommRingCat.ofHom (algebraMap k B)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap k E)) :=
  Under.homMk (CommRingCat.ofHom f.toRingHom) (CommRingCat.hom_ext (RingHom.ext f.commutes))

/-- 代数射の等しさを基底の下の圏で確認する。 -/
theorem underMap_injective {B E : Type u} [CommRing B] [CommRing E] [Algebra k B] [Algebra k E] :
    Function.Injective (underMap (k := k) (B := B) (E := E)) := by
  intro f g h
  ext1 x
  exact congrArg (fun v => v.right.hom x) h

end PDCechNerve

open PDCechNerve

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
variable (p : ℕ) {J : Ideal k} (γ : DividedPowers J) (hp : (p : k) ∈ J)
variable (hJ : J ≤ RingHom.ker (algebraMap k A)) {S : Type u} (s : S → A)

/-- 枠の評価の核を各次数で完備分冪包にした余単体的代数。 -/
@[expose] def pdCechNerve : Cosimplicial.CosimplicialAlgebra k where
  obj n := Under.mk (CommRingCat.ofHom (algebraMap k (term p γ hp hJ s n.len).carrier))
  map θ := underMap (mapCopies p γ hp hJ s θ.toOrderHom)
  map_id n := by
    apply Under.UnderMorphism.ext
    exact congrArg (fun f => CommRingCat.ofHom (AlgHom.toRingHom f))
      (mapCopies_id p γ hp hJ s n.len)
  map_comp f g := by
    apply Under.UnderMorphism.ext
    exact congrArg (fun f => CommRingCat.ofHom (AlgHom.toRingHom f))
      (mapCopies_comp p γ hp hJ s f.toOrderHom g.toOrderHom)

/-- 第零項から剰余環への増大。 -/
@[expose] def pdCechAugmentation : ((pdCechNerve p γ hp hJ s).obj ⦋0⦌).right →+* A :=
  (augmentation p γ hp hJ s 0).toRingHom

namespace PDCechNerve

variable {S' : Type u} (s' : S' → A)
local notation "D" => term p γ hp hJ
local notation "v" => variableImage p γ hp hJ
local notation "c" => mapCopies p γ hp hJ
local notation "aug" => augmentation p γ hp hJ
variable (φ : S → (term p γ hp hJ s' 0).carrier)
  (hφ : ∀ t, augmentation p γ hp hJ s' 0 (φ t) = s t)

/-- 枠の第零項の写像を各頂点へ入れた分冪射。 -/
def mapAt (n : ℕ) : (D s n).carrier →ₐ[k] (D s' n).carrier :=
  mapVariables p γ hp hJ s s' (m := n) (n := n)
    (fun x => c s' (m := 0) (n := n) (fun _ => x.2) (φ x.1))
    (fun x => (augmentation_mapCopies p γ hp hJ s' (m := 0) (n := n) _ _).trans (hφ x.1))

@[simp]
theorem mapAt_variableImage (n : ℕ) (x : S × Fin (n + 1)) :
    mapAt p γ hp hJ s s' φ hφ n (v s n x) = c s' (m := 0) (n := n) (fun _ => x.2) (φ x.1) :=
  mapVariables_variableImage p γ hp hJ s s' (m := n) (n := n) _ _ x

theorem mapAt_isDPMorphism (n : ℕ) :
    (D s n).dividedPowers.IsDPMorphism (D s' n).dividedPowers
      (mapAt p γ hp hJ s s' φ hφ n).toRingHom :=
  mapVariables_isDPMorphism p γ hp hJ s s' (m := n) (n := n) _ _

@[simp]
theorem augmentation_mapAt (n : ℕ) (x : (D s n).carrier) :
    aug s' n (mapAt p γ hp hJ s s' φ hφ n x) = aug s n x := by
  have he : (aug s' n).comp (mapAt p γ hp hJ s s' φ hφ n) = aug s n := by
    apply hom_ext p γ hp hJ s (complete_target p hp hJ)
      ((augmentation_isDPMorphism p γ hp hJ s' n).comp _
        (mapAt_isDPMorphism p γ hp hJ s s' φ hφ n))
      (augmentation_isDPMorphism p γ hp hJ s n)
    intro y
    simp [hφ]
  exact DFunLike.congr_fun he x

/-- 枠の射は頂点の添字の写像と可換。 -/
theorem mapAt_naturality {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) :
    (mapAt p γ hp hJ s s' φ hφ n).comp (c s (m := m) (n := n) θ) =
      (c s' (m := m) (n := n) θ).comp (mapAt p γ hp hJ s s' φ hφ m) := by
  apply hom_ext p γ hp hJ s (D s' n).isEnvelope.complete
    ((mapAt_isDPMorphism p γ hp hJ s s' φ hφ n).comp _
      (mapCopies_isDPMorphism p γ hp hJ s (m := m) (n := n) θ))
    ((mapCopies_isDPMorphism p γ hp hJ s' (m := m) (n := n) θ).comp _
      (mapAt_isDPMorphism p γ hp hJ s s' φ hφ m))
  intro x
  simp only [AlgHom.comp_apply, mapCopies_variableImage, mapAt_variableImage]
  exact DFunLike.congr_fun
    (mapCopies_comp p γ hp hJ s' (m := 0) (n := m) (l := n) (fun _ => x.2) θ) (φ x.1)

end PDCechNerve

/-- 枠の変数の第零項での像が同じ剰余元を持つとき、余単体的分冪射を誘導する。 -/
@[expose] def pdCechNerveMap {S' : Type u} (s' : S' → A)
    (φ : S → ((pdCechNerve p γ hp hJ s').obj ⦋0⦌).right)
    (hφ : ∀ t, pdCechAugmentation p γ hp hJ s' (φ t) = s t) :
    pdCechNerve p γ hp hJ s ⟶ pdCechNerve p γ hp hJ s' where
  app n := underMap (mapAt p γ hp hJ s s' φ hφ n.len)
  naturality {m n} θ := by
    apply Under.UnderMorphism.ext
    exact congrArg (fun f => CommRingCat.ofHom (AlgHom.toRingHom f))
      (mapAt_naturality p γ hp hJ s s' φ hφ θ.toOrderHom)

end SerrePositivity.BhattScholze.Prismatic
