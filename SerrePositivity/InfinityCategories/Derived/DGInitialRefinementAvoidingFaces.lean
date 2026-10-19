module
public import SerrePositivity.InfinityCategories.Derived.DGSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Derived.DGSimplexComponentExt
public import SerrePositivity.InfinityCategories.DGNerve.Pullback

/-! # 閉始点細分は始点を含まない面を厳密に保存する

概要：頂点零を避ける任意の単射制限では、始点細分後の全データが元と一致する。
方針：制限の各頂点は正なので、全 Hom の線形写像は等式輸送だけになる。
規約：退化制限は主張しない。使われ方：高次ホーンの元の終端面の保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 頂点零を避ける単射制限では、細分後の実データは元のデータと厳密に同じ。 -/
lemma dgSimplexDataInitialRefinement_pullback_avoids_zero {m n : ℕ} (t : SimplexData A D n)
    (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) (t.obj 0))
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α) (hz : ∀ i, α i ≠ 0) :
    (dgSimplexDataInitialRefinement A D t q s).pullback α = t.pullback α := by
  apply dgSimplexData_ext_of_components A D
  · intro i
    exact dgSourceRefinementObj_ne_zero D t.obj q (α i) (hz i)
  · intro I a b k hI ha hb hk
    rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hα.injOn,
      SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hα.injOn]
    dsimp only [dgSimplexDataInitialRefinement]
    exact (heq_of_eq (dgSourceRefinementHomLinear_of_ne_zero A D t.obj q s
      (α a) (α b) (hz a) (hz b) k _)).trans (gradedHomTransport_heq _ _ rfl _)

/-- 頂点零を避ける単射制限では、細分後の実単体は元の実単体と厳密に同じ。 -/
lemma dgSimplexInitialRefinement_pullback_avoids_zero {m n : ℕ} (t : Simplex A D n)
    (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) (t.obj 0))
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α) (hz : ∀ i, α i ≠ 0) :
    (dgSimplexInitialRefinement A D t q s).pullback α = t.pullback α := by
  apply Simplex.ext
  exact dgSimplexDataInitialRefinement_pullback_avoids_zero A D t.toSimplexData q s α hα hz

/-- 閉始点細分は、任意次数の実単体の零面を厳密に保存する。 -/
lemma dgSimplexInitialRefinement_face_zero {n : ℕ} (t : Simplex A D (n + 1))
    (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) (t.obj 0)) :
    (dgSimplexInitialRefinement A D t q s).pullback
      (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom =
      t.pullback (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom :=
  dgSimplexInitialRefinement_pullback_avoids_zero A D t q s _
    (0 : Fin (n + 2)).succAboveOrderEmb.injective
    (fun i => by change i.succ ≠ 0; exact Fin.succ_ne_zero i)

end SerrePositivity.InfinityCategories
