module
public import SerrePositivity.InfinityCategories.DGNerve.HornData
public import Mathlib.Data.Finset.Sort

/-! # ホーンの面の斉次成分の整合性

概要：同じ部分集合に対応する斉次成分を、利用可能な二つの面から回収して比較する。
方針：部分集合の有限順序による列挙を補助的に用い、ホーン内の共通の単体への制限で比較する。
規約：HA Proposition 1.3.1.10。単体の添字は従来の有限部分集合のままとする。
使われ方：既知成分の面の選択独立性とホーンの貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

namespace HomFamily

/-- 概要：対象族が等しく各成分が異種等号で一致する射族は、射族全体でも異種等号で一致する。
方針：対象族の等式を消去し、関数の外延性を各引数に適用する。
規約：HA Construction 1.3.1.6。使われ方：ホーン面への制限のデータの外延性。 -/
lemma heq_of_pointwise {n : ℕ} {obj obj' : Fin (n + 1) → D} (hobj : obj = obj')
    (f : HomFamily A D obj) (g : HomFamily A D obj')
    (h : ∀ I a b k hI ha hb hk, HEq (f I a b k hI ha hb hk) (g I a b k hI ha hb hk)) :
    HEq f g := by
  subst obj'
  apply heq_of_eq
  funext I a b k hI ha hb hk
  exact eq_of_heq (h I a b k hI ha hb hk)

end HomFamily

namespace SimplexData

/-- 概要：同じ単体データの成分は、集合・端点の等式に沿って異種等号で一致する。
方針：添字の等式を消去し、証明の一意性を使う。
規約：HA Construction 1.3.1.6。使われ方：共通の制限で比較した成分を元の添字へ戻す。 -/
lemma hom_heq_of_indices {n : ℕ} (s : SimplexData A D n)
    (I J : Finset (Fin (n + 1))) (a b c d : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (Index.nonempty hI))
    (hb : b = I.max' (Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (hJ : 2 ≤ J.card) (hc : c = J.min' (Index.nonempty hJ))
    (hd : d = J.max' (Index.nonempty hJ)) (hk' : k = 2 - (J.card : ℤ))
    (hIJ : I = J) (hac : a = c) (hbd : b = d) :
    HEq (s.hom I a b k hI ha hb hk) (s.hom J c d k hJ hc hd hk') := by
  subst J; subst c; subst d
  rfl

end SimplexData

namespace Simplex

/-- 概要：等しい単体の同じ成分は異種等号で一致する。
方針：単体の等式を消去する。
規約：HA Construction 1.3.1.6。使われ方：自然性の単体の等式を斉次成分に評価する。 -/
lemma hom_heq_of_eq {n : ℕ} {s t : Simplex A D n} (hst : s = t)
    (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : b = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)) :
    HEq (s.hom J a b k hJ ha hb hk) (t.hom J a b k hJ ha hb hk) := by
  subst t
  rfl

/-- 概要：二つの単射による制限が等しいなら、像の部分集合の成分は異種等号で一致する。
方針：制限の等式を成分で評価し、引き戻しの単射分岐を両側で使う。
規約：HA Proposition 1.3.1.10。使われ方：二つのホーン面の重なりの成分の比較。 -/
lemma hom_heq_of_pullback_eq {l m n : ℕ} (s : Simplex A D m) (t : Simplex A D n)
    (α : Fin (l + 1) →o Fin (m + 1)) (β : Fin (l + 1) →o Fin (n + 1))
    (h : s.pullback α = t.pullback β)
    (J : Finset (Fin (l + 1))) (a b : Fin (l + 1)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : b = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ))
    (hα : Set.InjOn α (J : Set (Fin (l + 1))))
    (hβ : Set.InjOn β (J : Set (Fin (l + 1)))) :
    HEq (s.hom (J.image α) (α a) (α b) k (Index.image_two hα hJ)
      (Index.image_min α.monotone (by rw [ha]; exact J.isLeast_min' _) _)
      (Index.image_max α.monotone (by rw [hb]; exact J.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injOn hα]; exact hk))
      (t.hom (J.image β) (β a) (β b) k (Index.image_two hβ hJ)
      (Index.image_min β.monotone (by rw [ha]; exact J.isLeast_min' _) _)
      (Index.image_max β.monotone (by rw [hb]; exact J.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injOn hβ]; exact hk)) := by
  have hh := hom_heq_of_eq h J a b k hJ ha hb hk
  change HEq ((s.toSimplexData.pullback α).hom J a b k hJ ha hb hk)
    ((t.toSimplexData.pullback β).hom J a b k hJ ha hb hk) at hh
  rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hα,
    SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hβ] at hh
  exact hh

end Simplex

namespace HornData

/-- 概要：二つの利用可能な面の同じ大域部分集合に対応する斉次成分は異種等号で一致する。
方針：第一の集合を有限順序で列挙し、そのホーン内の単体への二つの制限を自然性で比較する。
規約：HA Proposition 1.3.1.10。使われ方：既知成分を回収する面の選択独立性。 -/
lemma face_hom_heq {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ dgNerve A D)
    (j l : Fin (n + 3)) (hji : j ≠ i) (hli : l ≠ i)
    (J L : Finset (Fin (n + 2))) (a b c d : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : b = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ))
    (hL : 2 ≤ L.card) (hc : c = L.min' (Index.nonempty hL))
    (hd : d = L.max' (Index.nonempty hL)) (hk' : k = 2 - (L.card : ℤ))
    (hImage : J.image j.succAbove = L.image l.succAbove) :
    HEq ((σ.app _ (SSet.horn.face i j hji)).hom J a b k hJ ha hb hk)
      ((σ.app _ (SSet.horn.face i l hli)).hom L c d k hL hc hd hk') := by
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
  have hres : (σ.app _ (SSet.horn.face i j hji)).pullback φ.toOrderHom =
      (σ.app _ (SSet.horn.face i l hli)).pullback β.toOrderHom := by
    have hh := HornFaces.restriction_independent i σ θ j l hji hli hθj hθl
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
  let a₀ := E.min' (Index.nonempty hE)
  let b₀ := E.max' (Index.nonempty hE)
  have hαa : φ.toOrderHom a₀ = a := by
    rw [ha]
    simpa only [hαI] using Index.image_min φ.toOrderHom.monotone
      (E.isLeast_min' (Index.nonempty hE)) (Finset.Nonempty.image (Index.nonempty hE) _)
  have hαb : φ.toOrderHom b₀ = b := by
    rw [hb]
    simpa only [hαI] using Index.image_max φ.toOrderHom.monotone
      (E.isGreatest_max' (Index.nonempty hE)) (Finset.Nonempty.image (Index.nonempty hE) _)
  have hβc : β.toOrderHom a₀ = c := by
    rw [hc]
    simpa only [hβI] using Index.image_min β.toOrderHom.monotone
      (E.isLeast_min' (Index.nonempty hE)) (Finset.Nonempty.image (Index.nonempty hE) _)
  have hβd : β.toOrderHom b₀ = d := by
    rw [hd]
    simpa only [hβI] using Index.image_max β.toOrderHom.monotone
      (E.isGreatest_max' (Index.nonempty hE)) (Finset.Nonempty.image (Index.nonempty hE) _)
  have H := Simplex.hom_heq_of_pullback_eq _ _ φ.toOrderHom β.toOrderHom hres E a₀ b₀ k
    hE rfl rfl (by simpa only [E, Finset.card_univ, Fintype.card_fin, ← hcard] using hk)
    e.injective.injOn hβinj.injOn
  cases hαa
  cases hαb
  cases hβc
  cases hβd
  simpa only [hαI, hβI] using H

/-- 概要：回収した既知成分は、その集合を含む任意の利用可能な面の成分と異種等号で一致する。
方針：回収時の二つの移送を異種等号で外し、共通の集合を持つ二面の成分の一致を使う。
規約：HA Proposition 1.3.1.10。使われ方：回収の選択独立性と面への制限の検証。 -/
lemma recoverHom_heq_face {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ dgNerve A D)
    (I : Finset (Fin (n + 3))) (a b : Fin (n + 3)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (Index.nonempty hI))
    (hb : b = I.max' (Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (hfull : I ≠ Finset.univ) (hmissing : I ≠ Finset.univ.erase i)
    (j : Fin (n + 3)) (hji : j ≠ i) (J : Finset (Fin (n + 2)))
    (c d : Fin (n + 2)) (hJ : 2 ≤ J.card)
    (hc : c = J.min' (Index.nonempty hJ)) (hd : d = J.max' (Index.nonempty hJ))
    (hk' : k = 2 - (J.card : ℤ)) (hImage : J.image j.succAbove = I) :
    HEq (recoverHom σ I a b k hI ha hb hk hfull hmissing)
      ((σ.app _ (SSet.horn.face i j hji)).hom J c d k hJ hc hd hk') := by
  unfold recoverHom
  refine (cast_heq _ _).trans ?_
  refine (componentOnFace_heq σ _ _ _ _ _ _ _ _ _ _).trans ?_
  apply face_hom_heq σ
  exact (HornIndex.image_preimage I _ (HornIndex.coveringFace_notMem I i hfull hmissing)).trans
    hImage.symm

end HornData

end SerrePositivity.InfinityCategories.DGNerve
