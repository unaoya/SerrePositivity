module
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra.FrameHelpers
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra.FrameHelpers

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Homotopy
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# 枠を取り替える分冪 Čech 脈体の余鎖ホモトピー

## 概要
剰余環を覆う二つの枠の間の射は、交代余面複体の擬同型を誘導する。

## 方針
二つの枠の射の変数像を頂点の順に切り替え、余単体ホモトピーを作る。
逆向きの変数像は剰余環の各元の持ち上げから選ぶ。

## 規約
非正規化の交代余面複体を使う。ホモトピーは完備分冪包の普遍性から
各次数で直接作る。Stacks 07HP の持ち上げによる比較に対応する。

## 使われ方
BS 著者版 Theorem 5.2 の多項式模型での枠の取り替え。
-/

public noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic
namespace PDCechNerve

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
variable (p : ℕ) {J : Ideal k} (γ : DividedPowers J) (hp : (p : k) ∈ J)
variable (hJ : J ≤ RingHom.ker (algebraMap k A))
variable {S T : Type u} (s : S → A) (t : T → A)
variable (f g : S → (term p γ hp hJ t 0).carrier)
variable (hf : ∀ x, augmentation p γ hp hJ t 0 (f x) = s x)
variable (hg : ∀ x, augmentation p γ hp hJ t 0 (g x) = s x)

local notation "D" => term p γ hp hJ
local notation "v" => variableImage p γ hp hJ
local notation "c" => mapCopies p γ hp hJ
local notation "aug" => augmentation p γ hp hJ
local notation "atLevel" => mapAt p γ hp hJ
local notation "N" => pdCechNerve p γ hp hJ
local notation "Nmap" => pdCechNerveMap p γ hp hJ

private def prism {n : ℕ} (i : Fin (n + 1)) :
    (D s (n + 1)).carrier →ₐ[k] (D t n).carrier :=
  mapVariables p γ hp hJ s t (m := n + 1) (n := n)
    (fun x => c t (m := 0) (n := n) (fun _ => i.predAbove x.2)
      ((if x.2 ≤ i.castSucc then f else g) x.1))
    (fun x => by
      rw [augmentation_mapCopies]
      split_ifs <;> first | exact hf x.1 | exact hg x.1)

private theorem prism_isDPMorphism {n : ℕ} (i : Fin (n + 1)) :
    (D s (n + 1)).dividedPowers.IsDPMorphism (D t n).dividedPowers
      (prism p γ hp hJ s t f g hf hg i).toRingHom :=
  mapVariables_isDPMorphism p γ hp hJ s t (m := n + 1) (n := n) _ _

private theorem prism_variableImage {n : ℕ} (i : Fin (n + 1)) (x : S × Fin (n + 2)) :
    prism p γ hp hJ s t f g hf hg i (v s (n + 1) x) =
      c t (m := 0) (n := n) (fun _ => i.predAbove x.2)
        ((if x.2 ≤ i.castSucc then f else g) x.1) :=
  mapVariables_variableImage p γ hp hJ s t (m := n + 1) (n := n) _ _ x

local notation "H" => prism p γ hp hJ s t f g hf hg
local notation "Hdp" => prism_isDPMorphism p γ hp hJ s t f g hf hg
local notation "Cdp" => mapCopies_isDPMorphism p γ hp hJ
local notation "Fdp" => mapAt_isDPMorphism p γ hp hJ s t

private theorem prism_zero (n : ℕ) :
    (H (0 : Fin (n + 1))).comp (c s (m := n) (n := n + 1) (Fin.succAbove 0)) =
      atLevel s t g hg n := by
  apply hom_ext p γ hp hJ s (D t n).isEnvelope.complete
    ((Hdp (0 : Fin (n + 1))).comp _ (Cdp s (m := n) (n := n + 1) (Fin.succAbove 0)))
    (Fdp g hg n)
  rintro ⟨x, j⟩
  simp only [AlgHom.comp_apply, mapCopies_variableImage, prism_variableImage, mapAt_variableImage]
  have h : ¬ (0 : Fin (n + 2)).succAbove j ≤ (0 : Fin (n + 1)).castSucc := by
    change ¬ ((0 : Fin (n + 2)).succAbove j).val ≤ 0
    rw [val_succAbove]
    simp
  rw [ite_eq_right h]
  congr 1

private theorem prism_last (n : ℕ) :
    (H (Fin.last n)).comp (c s (m := n) (n := n + 1) (Fin.succAbove (Fin.last (n + 1)))) =
      atLevel s t f hf n := by
  apply hom_ext p γ hp hJ s (D t n).isEnvelope.complete
    ((Hdp (Fin.last n)).comp _ (Cdp s (m := n) (n := n + 1) (Fin.succAbove (Fin.last (n + 1)))))
    (Fdp f hf n)
  rintro ⟨x, j⟩
  simp only [AlgHom.comp_apply, mapCopies_variableImage, prism_variableImage, mapAt_variableImage]
  have h : (Fin.last (n + 1)).succAbove j ≤ (Fin.last n).castSucc := by
    have hj := j.isLt
    simp only [Fin.le_def, val_succAbove, Fin.val_last, Fin.val_castSucc,
      ite_eq_left hj]
    omega
  rw [ite_eq_left h]
  apply congrArg (fun a : Fin (n + 1) => c t (m := 0) (n := n) (fun _ => a) (f x))
  apply Fin.ext
  have hj := j.isLt
  simp only [val_succAbove, val_predAbove, Fin.val_last, ite_eq_left hj]
  split_ifs <;> omega

private theorem prism_δ_left {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    (H j.succ).comp (c s (m := n + 1) (n := n + 2) (Fin.succAbove i.castSucc)) =
      (c t (m := n) (n := n + 1) (Fin.succAbove i)).comp (H j) := by
  apply hom_ext p γ hp hJ s (D t (n + 1)).isEnvelope.complete
    ((Hdp j.succ).comp _ (Cdp s (m := n + 1) (n := n + 2) (Fin.succAbove i.castSucc)))
    ((Cdp t (m := n) (n := n + 1) (Fin.succAbove i)).comp _ (Hdp j))
  rintro ⟨x, a⟩
  simp only [AlgHom.comp_apply, mapCopies_variableImage, prism_variableImage, mapCopies_mapCopies]
  simp only [Fin.le_def, Fin.val_castSucc] at hij
  congr 1
  · apply congrArg (c t (m := 0))
    funext z
    apply Fin.ext
    simp only [Function.comp_apply, val_succAbove, val_predAbove, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega
  · apply congrArg (fun h : S → (D t 0).carrier => h x)
    apply if_congr _ rfl rfl
    simp only [Fin.le_def, val_succAbove, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega

private theorem prism_δ_middle {n : ℕ} (j : Fin (n + 1)) :
    (H j.succ).comp (c s (m := n + 1) (n := n + 2) (Fin.succAbove j.castSucc.succ)) =
      (H j.castSucc).comp (c s (m := n + 1) (n := n + 2) (Fin.succAbove j.castSucc.succ)) := by
  apply hom_ext p γ hp hJ s (D t (n + 1)).isEnvelope.complete
    ((Hdp j.succ).comp _ (Cdp s (m := n + 1) (n := n + 2) (Fin.succAbove j.castSucc.succ)))
    ((Hdp j.castSucc).comp _ (Cdp s (m := n + 1) (n := n + 2) (Fin.succAbove j.castSucc.succ)))
  rintro ⟨x, a⟩
  simp only [AlgHom.comp_apply, mapCopies_variableImage, prism_variableImage]
  congr 1
  · apply congrArg (c t (m := 0))
    funext z
    apply Fin.ext
    simp only [val_succAbove, val_predAbove, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega
  · apply congrArg (fun h : S → (D t 0).carrier => h x)
    apply if_congr _ rfl rfl
    simp only [Fin.le_def, val_succAbove, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega

private theorem prism_δ_right {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    (H j.castSucc).comp (c s (m := n + 1) (n := n + 2) (Fin.succAbove i.succ)) =
      (c t (m := n) (n := n + 1) (Fin.succAbove i)).comp (H j) := by
  apply hom_ext p γ hp hJ s (D t (n + 1)).isEnvelope.complete
    ((Hdp j.castSucc).comp _ (Cdp s (m := n + 1) (n := n + 2) (Fin.succAbove i.succ)))
    ((Cdp t (m := n) (n := n + 1) (Fin.succAbove i)).comp _ (Hdp j))
  rintro ⟨x, a⟩
  simp only [AlgHom.comp_apply, mapCopies_variableImage, prism_variableImage, mapCopies_mapCopies]
  simp only [Fin.lt_def, Fin.val_castSucc] at hji
  congr 1
  · apply congrArg (c t (m := 0))
    funext z
    apply Fin.ext
    simp only [Function.comp_apply, val_succAbove, val_predAbove, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega
  · apply congrArg (fun h : S → (D t 0).carrier => h x)
    apply if_congr _ rfl rfl
    simp only [Fin.le_def, val_succAbove, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega

private theorem prism_σ_left {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    (H j).comp (c s (m := n + 2) (n := n + 1) (Fin.predAbove i.castSucc)) =
      (c t (m := n + 1) (n := n) (Fin.predAbove i)).comp (H j.succ) := by
  apply hom_ext p γ hp hJ s (D t n).isEnvelope.complete
    ((Hdp j).comp _ (Cdp s (m := n + 2) (n := n + 1) (Fin.predAbove i.castSucc)))
    ((Cdp t (m := n + 1) (n := n) (Fin.predAbove i)).comp _ (Hdp j.succ))
  rintro ⟨x, a⟩
  simp only [AlgHom.comp_apply, mapCopies_variableImage, prism_variableImage, mapCopies_mapCopies]
  simp only [Fin.le_def] at hij
  congr 1
  · apply congrArg (c t (m := 0))
    funext z
    apply Fin.ext
    simp only [Function.comp_apply, val_predAbove, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega
  · apply congrArg (fun h : S → (D t 0).carrier => h x)
    apply if_congr _ rfl rfl
    simp only [Fin.le_def, val_predAbove, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega

private theorem prism_σ_right {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    (H j).comp (c s (m := n + 2) (n := n + 1) (Fin.predAbove i.succ)) =
      (c t (m := n + 1) (n := n) (Fin.predAbove i)).comp (H j.castSucc) := by
  apply hom_ext p γ hp hJ s (D t n).isEnvelope.complete
    ((Hdp j).comp _ (Cdp s (m := n + 2) (n := n + 1) (Fin.predAbove i.succ)))
    ((Cdp t (m := n + 1) (n := n) (Fin.predAbove i)).comp _ (Hdp j.castSucc))
  rintro ⟨x, a⟩
  simp only [AlgHom.comp_apply, mapCopies_variableImage, prism_variableImage, mapCopies_mapCopies]
  simp only [Fin.le_def] at hji
  congr 1
  · apply congrArg (c t (m := 0))
    funext z
    apply Fin.ext
    simp only [Function.comp_apply, val_predAbove, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega
  · apply congrArg (fun h : S → (D t 0).carrier => h x)
    apply if_congr _ rfl rfl
    simp only [Fin.le_def, val_predAbove, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega

private def simplicialHomotopy :
    SimplicialObject.Homotopy
      ((cosimplicialSimplicialEquiv _).functor.map (Nmap s t f hf).op)
      ((cosimplicialSimplicialEquiv _).functor.map (Nmap s t g hg).op) where
  h i := (underMap (H i)).op
  h_zero_comp_δ_zero n :=
    Quiver.Hom.unop_inj (congrArg underMap (prism_zero p γ hp hJ s t f g hf hg n))
  h_last_comp_δ_last n :=
    Quiver.Hom.unop_inj (congrArg underMap (prism_last p γ hp hJ s t f g hf hg n))
  h_succ_comp_δ_castSucc_of_lt i j hij :=
    Quiver.Hom.unop_inj (congrArg underMap (prism_δ_left p γ hp hJ s t f g hf hg i j hij))
  h_succ_comp_δ_castSucc_succ j :=
    Quiver.Hom.unop_inj (congrArg underMap (prism_δ_middle p γ hp hJ s t f g hf hg j))
  h_castSucc_comp_δ_succ_of_lt i j hji :=
    Quiver.Hom.unop_inj (congrArg underMap (prism_δ_right p γ hp hJ s t f g hf hg i j hji))
  h_comp_σ_castSucc_of_le i j hij :=
    Quiver.Hom.unop_inj (congrArg underMap (prism_σ_left p γ hp hJ s t f g hf hg i j hij))
  h_comp_σ_succ_of_lt i j hji :=
    Quiver.Hom.unop_inj (congrArg underMap (prism_σ_right p γ hp hJ s t f g hf hg i j hji))

/-- 同じ剰余環上の二つの枠の射は、交代余面複体では余鎖ホモトピーで結ばれる。 -/
def cochainHomotopy :
    Homotopy ((alternatingCofaceMapComplex _).map
      (Functor.whiskerRight (Nmap s t f hf) (algebraModule k)))
      ((alternatingCofaceMapComplex _).map
        (Functor.whiskerRight (Nmap s t g hg) (algebraModule k))) :=
  Cosimplicial.CosimplicialHomotopy.toCochainHomotopy
    ((simplicialHomotopy p γ hp hJ s t f g hf hg).whiskerRight (algebraModule k).op)

/-- 各変数を第零項の同じ変数へ送る枠の射は恒等射。 -/
theorem nerveMap_id :
    Nmap s s (fun x => v s 0 (x, 0)) (fun x => by
      change aug s 0 (v s 0 (x, 0)) = s x
      exact augmentation_variableImage p γ hp hJ s 0 (x, 0)) = 𝟙 (N s) := by
  apply NatTrans.ext
  funext n
  have h : atLevel s s (fun x => v s 0 (x, 0)) (fun _ => by simp) n.len =
      AlgHom.id k (D s n.len).carrier := by
    apply hom_ext p γ hp hJ s (D s n.len).isEnvelope.complete
      (mapAt_isDPMorphism p γ hp hJ s s _ _ _)
      (DividedPowers.DPMorphism.id (D s n.len).dividedPowers).isDPMorphism
    rintro ⟨x, j⟩
    simp
  exact congrArg underMap h

variable {U : Type u} (w : U → A)
variable (b : T → (term p γ hp hJ w 0).carrier)
variable (hb : ∀ x, augmentation p γ hp hJ w 0 (b x) = t x)

/-- 枠の二つの射の合成は第零項の合成で与えられる。 -/
theorem nerveMap_comp :
    Nmap s t f hf ≫ Nmap t w b hb =
      Nmap s w (fun x => atLevel t w b hb 0 (f x))
        (fun x => (augmentation_mapAt p γ hp hJ t w b hb 0 (f x)).trans (hf x)) := by
  apply NatTrans.ext
  funext n
  let f₀ := fun x => atLevel t w b hb 0 (f x)
  have hf₀ : ∀ x, aug w 0 (f₀ x) = s x := by intro x; simp [f₀, hf]
  have h : (atLevel t w b hb n.len).comp (atLevel s t f hf n.len) =
      atLevel s w f₀ hf₀ n.len := by
    apply hom_ext p γ hp hJ s (D w n.len).isEnvelope.complete
      ((mapAt_isDPMorphism p γ hp hJ t w b hb n.len).comp _
        (mapAt_isDPMorphism p γ hp hJ s t f hf n.len))
      (mapAt_isDPMorphism p γ hp hJ s w f₀ hf₀ n.len)
    rintro ⟨x, j⟩
    simp only [AlgHom.comp_apply, mapAt_variableImage]
    exact DFunLike.congr_fun
      (mapAt_naturality p γ hp hJ t w b hb (m := 0) (n := n.len) (fun _ => j)) (f x)
  exact congrArg underMap h

end PDCechNerve

open PDCechNerve

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
variable (p : ℕ) {J : Ideal k} (γ : DividedPowers J) (hp : (p : k) ∈ J)
variable (hJ : J ≤ RingHom.ker (algebraMap k A))
variable {S T : Type u} (s : S → A) (t : T → A)
variable (f : S → ((pdCechNerve p γ hp hJ t).obj ⦋0⦌).right)
variable (hf : ∀ x, pdCechAugmentation p γ hp hJ t (f x) = s x)

private theorem augmentation_surjective (hs : Function.Surjective (pdFrameEval (k := k) s 0)) :
    Function.Surjective (pdCechAugmentation p γ hp hJ s) := by
  intro x
  obtain ⟨y, hy⟩ := hs x
  exact ⟨(term p γ hp hJ s 0).unit y, (augmentation_unit p γ hp hJ s 0 y).trans hy⟩

/-- 概要：剰余環を覆う枠を取り替える射は交代余面複体で擬同型。
方針：逆向きの変数像を選ぶ。両側の合成を恒等射に結ぶ余鎖ホモトピーは
各頂点で二つの変数像を切り替えて作る。
規約：分冪包の普遍性で完備化した各項に直接写像を構成する。
使われ方：Theorem 6.4 の大きい分冪模型と小さい分冪模型の比較。 -/
theorem pdCechNerveMap_quasiIso
    (_hk : IsAdicComplete (Ideal.span {(p : k)}) k)
    (hs : Function.Surjective (pdFrameEval (k := k) s 0))
    (_ht : Function.Surjective (pdFrameEval (k := k) t 0)) :
    QuasiIso ((alternatingCofaceMapComplex _).map
      (Functor.whiskerRight (pdCechNerveMap p γ hp hJ s t f hf)
        (algebraModule k))) := by
  classical
  let r := fun x => (augmentation_surjective p γ hp hJ s hs (t x)).choose
  have hr : ∀ x, pdCechAugmentation p γ hp hJ s (r x) = t x :=
    fun x => (augmentation_surjective p γ hp hJ s hs (t x)).choose_spec
  let F := (Functor.whiskeringRight SimplexCategory _ _).obj
      (algebraModule k) ⋙ alternatingCofaceMapComplex _
  let j := pdCechNerveMap p γ hp hJ s t f hf
  let j' := pdCechNerveMap p γ hp hJ t s r hr
  change QuasiIso (F.map j)
  let e : HomotopyEquiv (F.obj (pdCechNerve p γ hp hJ s)) (F.obj (pdCechNerve p γ hp hJ t)) :=
    { hom := F.map j
      inv := F.map j'
      homotopyHomInvId := by
        rw [← F.map_comp, ← F.map_id]
        change Homotopy (F.map (pdCechNerveMap p γ hp hJ s t f hf ≫
          pdCechNerveMap p γ hp hJ t s r hr)) _
        rw [nerveMap_comp p γ hp hJ s t f hf s r hr, ← nerveMap_id p γ hp hJ s]
        exact cochainHomotopy p γ hp hJ s s _ _ _ _
      homotopyInvHomId := by
        rw [← F.map_comp, ← F.map_id]
        change Homotopy (F.map (pdCechNerveMap p γ hp hJ t s r hr ≫
          pdCechNerveMap p γ hp hJ s t f hf)) _
        rw [nerveMap_comp p γ hp hJ t s r hr t f hf, ← nerveMap_id p γ hp hJ t]
        exact cochainHomotopy p γ hp hJ t t _ _ _ _ }
  exact e.quasiIso_hom

end SerrePositivity.BhattScholze.Prismatic
