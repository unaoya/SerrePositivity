module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechAffineFrameQuasiIso
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechFrameHomotopy
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechAffineFrameQuasiIso
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechFrameHomotopy

/-!
# 加法的関手で移した枠の比較

## 概要
有限・大きい affine 枠と分冪枠の比較は、任意の加法的関手で各項を移しても擬同型。

## 方針
既存の二つの合成の鎖ホモトピーからホモトピー同値を組み、関手で移す。

## 規約
関手の完全性や係数射の平坦性を仮定しない。ホモトピーを保つ加法性だけを使う。

## 使われ方
BS 著者版 Theorem 6.4、完備係数拡大後の大きい枠の二比較。
-/

public noncomputable section
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false

section PD
open PDCechNerve
variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B] [Algebra k A]
variable (p : ℕ) {J : Ideal k} (γ : DividedPowers J) (hp : (p : k) ∈ J)
variable (hJ : J ≤ RingHom.ker (algebraMap k A))
variable {S T : Type u} (s : S → A) (t : T → A)
variable (f : S → ((pdCechNerve p γ hp hJ t).obj ⦋0⦌).right)
variable (hf : ∀ x, pdCechAugmentation p γ hp hJ t (f x) = s x)
variable (F : ModuleCat.{u} k ⥤ ModuleCat.{u} B) [F.Additive]

/-- 分冪枠の比較は、任意の加法的関手を各項に適用しても擬同型。 -/
theorem pdCechNerveMap_map_quasiIso
    (hs : Function.Surjective (pdFrameEval (k := k) s 0)) :
    QuasiIso ((F.mapHomologicalComplex _).map
      ((alternatingCofaceMapComplex _).map
        (Functor.whiskerRight (pdCechNerveMap p γ hp hJ s t f hf) (algebraModule k)))) := by
  classical
  let r := fun x => (augmentation_surjective p γ hp hJ s hs (t x)).choose
  have hr : ∀ x, pdCechAugmentation p γ hp hJ s (r x) = t x :=
    fun x => (augmentation_surjective p γ hp hJ s hs (t x)).choose_spec
  let L := (Functor.whiskeringRight SimplexCategory _ _).obj
      (algebraModule k) ⋙ alternatingCofaceMapComplex _
  let j := pdCechNerveMap p γ hp hJ s t f hf
  let j' := pdCechNerveMap p γ hp hJ t s r hr
  let e : HomotopyEquiv (L.obj (pdCechNerve p γ hp hJ s))
      (L.obj (pdCechNerve p γ hp hJ t)) :=
    { hom := L.map j
      inv := L.map j'
      homotopyHomInvId := by
        rw [← L.map_comp, ← L.map_id]
        change Homotopy (L.map (pdCechNerveMap p γ hp hJ s t f hf ≫
          pdCechNerveMap p γ hp hJ t s r hr)) _
        rw [nerveMap_comp p γ hp hJ s t f hf s r hr, ← nerveMap_id p γ hp hJ s]
        exact cochainHomotopy p γ hp hJ s s _ _ _ _
      homotopyInvHomId := by
        rw [← L.map_comp, ← L.map_id]
        change Homotopy (L.map (pdCechNerveMap p γ hp hJ t s r hr ≫
          pdCechNerveMap p γ hp hJ s t f hf)) _
        rw [nerveMap_comp p γ hp hJ t s r hr t f hf, ← nerveMap_id p γ hp hJ t]
        exact cochainHomotopy p γ hp hJ t t _ _ _ _ }
  exact (F.mapHomotopyEquiv e).quasiIso_hom
end PD

section Affine
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (Q : Poly (A ⧸ P.ideal))
variable (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.Additive]
local notation "U" => fun n => affineEnvelopeTerm P hP Q.n n (polyCutoff P Q.n) le_rfl
local notation "E" => fun Q n => affineBigCechTerm P Q n hP
local notation "S" => prismSiteAlgebras P (polyCompletion P Q.n) (polyCutoff P Q.n)
local notation "G" => S ⋙ PDCechNerve.algebraModule A
local notation "M" => BigCechVertexFrame.model P Q E
  (fun n => affineBigCechTerm_bounded P Q n hP) (affineBigCechTerm_small P hP Q)
local notation "j" => BigCechVertexFrame.toBig P Q E
  (fun n => affineBigCechTerm_bounded P Q n hP) (affineBigCechTerm_small P hP Q) U
local notation "j'" => BigCechVertexFrame.toFinite P Q E
  (fun n => affineBigCechTerm_bounded P Q n hP) (affineBigCechTerm_small P hP Q) U

/-- affine の有限・大きい枠の比較は、任意の加法的関手を各項に適用しても擬同型。 -/
theorem affineCechAlexanderFrame_map_quasiIso :
    QuasiIso ((F.mapHomologicalComplex _).map
      ((alternatingCofaceMapComplex _).map
        (Functor.whiskerRight (affineCechAlexanderFrame (P := P) hP Q)
          (PDCechNerve.algebraModule A)))) := by
  let L := (Functor.whiskeringRight SimplexCategory _ _).obj
    (PDCechNerve.algebraModule A) ⋙ alternatingCofaceMapComplex _
  change QuasiIso ((F.mapHomologicalComplex _).map
    (L.map (affineCechAlexanderFrame (P := P) hP Q)))
  rw [← comparison_whisker P hP Q, L.map_comp, (F.mapHomologicalComplex _).map_comp]
  have hj : QuasiIso ((F.mapHomologicalComplex _).map
      (L.map (Functor.whiskerRight (j) S))) := by
    let K := (Functor.whiskeringRight SimplexCategory _ _).obj G ⋙ alternatingCofaceMapComplex _
    let e : HomotopyEquiv (K.obj (cechAlexanderOfAffineTerms P U)) (K.obj M) :=
      { hom := K.map (j)
        inv := K.map (j')
        homotopyHomInvId := by
          rw [← K.map_comp, ← K.map_id]
          exact BigCechVertexFrame.finiteCompositeHomotopy P Q E
            (fun n => affineBigCechTerm_bounded P Q n hP) (affineBigCechTerm_small P hP Q) U
        homotopyInvHomId := by
          rw [← K.map_comp, ← K.map_id]
          exact BigCechVertexFrame.bigCompositeHomotopy P Q E
            (fun n => affineBigCechTerm_bounded P Q n hP) (affineBigCechTerm_small P hP Q) U }
    exact (F.mapHomotopyEquiv e).quasiIso_hom
  infer_instance
end Affine
end SerrePositivity.BhattScholze.Prismatic
