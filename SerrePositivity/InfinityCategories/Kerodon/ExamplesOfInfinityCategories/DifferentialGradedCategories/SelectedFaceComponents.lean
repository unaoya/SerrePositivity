module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornComponents

/-! # 選んだ境界面の斉次成分の整合性

概要：同じ大域部分集合の成分は、それを含む選んだ面の選択によらない。
方針：N2 の順序付き列挙による比較を選んだ面の和に適用する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：N7c の境界成分の回収。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：二つの選んだ面の同じ大域部分集合に対応する斉次成分は異種等号で一致する。
方針：第一の集合を有限順序で列挙し、その部分境界内の単体への二つの制限を自然性で比較する。
規約：HA Proposition 1.3.1.10。使われ方：既知成分を回収する面の選択独立性。 -/
lemma face_hom_heq {n : ℕ} (S : Finset (Fin (n + 3)))
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region S : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (j l : Fin (n + 3)) (hjS : j ∈ S) (hlS : l ∈ S)
    (J L : Finset (Fin (n + 2))) (a b c d : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ))
    (hL : 2 ≤ L.card) (hc : c = L.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL))
    (hd : d = L.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL)) (hk' : k = 2 - (L.card : ℤ))
    (hImage : J.image j.succAbove = L.image l.succAbove) :
    HEq ((σ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face S j hjS)).hom J a b k hJ ha hb hk)
      ((σ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face S l hlS)).hom L c d k hL hc hd hk') := by
  let r := J.card - 1
  have hcard : J.card = r + 1 := by omega
  let e := J.orderEmbOfFin hcard
  let φ : ⦋r⦌ ⟶ ⦋n + 1⦌ := SimplexCategory.mkHom e.toOrderHom
  let θ : ⦋r⦌ ⟶ ⦋n + 2⦌ := φ ≫ SimplexCategory.δ j
  have hθj : ∀ x, θ.toOrderHom x ≠ j := fun x => Fin.succAbove_ne j (e x)
  have hθl : ∀ x, θ.toOrderHom x ≠ l := by
    intro x hx
    have hm : θ.toOrderHom x ∈ J.image j.succAbove :=
      Finset.mem_image.mpr ⟨e x, J.orderEmbOfFin_mem hcard x, rfl⟩
    rw [hImage, hx] at hm
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hm
    exact Fin.succAbove_ne l y hy
  let β := SimplexCategory.factor_δ θ l
  have hβδ := SimplexCategory.factor_δ_spec θ l hθl
  have hβ : ∀ x, l.succAbove (β.toOrderHom x) = j.succAbove (φ.toOrderHom x) := by
    intro x
    exact congrArg (fun f => f.toOrderHom x) hβδ
  have hβinj : Function.Injective β.toOrderHom := by
    intro x y hxy
    apply e.injective
    apply j.succAboveOrderEmb.injective
    exact (hβ x).symm.trans ((congrArg l.succAbove hxy).trans (hβ y))
  have hφ : SimplexCategory.factor_δ θ j = φ := by
    ext x : 3
    apply j.succAboveOrderEmb.injective
    exact congrArg (fun f => f.toOrderHom x) (SimplexCategory.factor_δ_spec θ j hθj)
  have hres : (σ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face S j hjS)).pullback φ.toOrderHom =
      (σ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face S l hlS)).pullback β.toOrderHom := by
    have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.restriction_independent S σ θ j l hjS hlS hθj hθl
    rw [hφ] at hh
    exact hh
  let E : Finset (Fin (r + 1)) := Finset.univ
  have hE : 2 ≤ E.card := by simpa only [E, Finset.card_univ, Fintype.card_fin, ← hcard] using hJ
  have hαI : E.image φ.toOrderHom = J := J.image_orderEmbOfFin_univ hcard
  have hβI : E.image β.toOrderHom = L := by
    apply Finset.image_injective l.succAboveOrderEmb.injective
    calc
      (E.image β.toOrderHom).image l.succAbove = E.image (fun x => l.succAbove (β.toOrderHom x)) :=
        Finset.image_image
      _ = E.image (fun x => j.succAbove (φ.toOrderHom x)) :=
        congrArg (fun f => E.image f) (funext hβ)
      _ = (E.image φ.toOrderHom).image j.succAbove := by rw [Finset.image_image]; rfl
      _ = J.image j.succAbove := by rw [hαI]
      _ = L.image l.succAbove := hImage
  let a₀ := E.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE)
  let b₀ := E.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE)
  have hαa : φ.toOrderHom a₀ = a := by
    rw [ha]
    simpa only [hαI] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min φ.toOrderHom.monotone
      (E.isLeast_min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE)) (Finset.Nonempty.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE) _)
  have hαb : φ.toOrderHom b₀ = b := by
    rw [hb]
    simpa only [hαI] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max φ.toOrderHom.monotone
      (E.isGreatest_max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE)) (Finset.Nonempty.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE) _)
  have hβc : β.toOrderHom a₀ = c := by
    rw [hc]
    simpa only [hβI] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min β.toOrderHom.monotone
      (E.isLeast_min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE)) (Finset.Nonempty.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE) _)
  have hβd : β.toOrderHom b₀ = d := by
    rw [hd]
    simpa only [hβI] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max β.toOrderHom.monotone
      (E.isGreatest_max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE)) (Finset.Nonempty.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE) _)
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.hom_heq_of_pullback_eq _ _ φ.toOrderHom β.toOrderHom hres E a₀ b₀ k
    hE rfl rfl (by simpa only [E, Finset.card_univ, Fintype.card_fin, ← hcard] using hk)
    e.injective.injOn hβinj.injOn
  cases hαa
  cases hαb
  cases hβc
  cases hβd
  simpa only [hαI, hβI] using H

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
