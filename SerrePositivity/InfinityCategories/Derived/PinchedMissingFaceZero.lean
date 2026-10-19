module
public import SerrePositivity.InfinityCategories.Derived.PinchedNormalizedFaces

/-! # 零の指定面に含まれる全成分と引き戻しの消滅

概要：指定面が零なら、その面に含まれる部分集合の成分と任意の単体の引き戻しは零。
方針：余面の preimage で成分を回収し、非単射な引き戻しの成分は定義から零にする。
規約：全ての次元の単調写像を許す。使われ方：錐 prism の境界上での消滅。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 指定面が零なら、欠落頂点を含まない全ての成分は零。 -/
lemma pinchedLinearData_component_zero_of_face {n : ℕ} (f : LinearData A x y (n + 1))
    (j : Fin (n + 2)) (hf : LinearData.pullback j.succAboveOrderEmb.toOrderHom f = 0)
    (I : Finset (Fin (n + 2))) (k : ℤ) (hI : I.Nonempty) (hk : k = 1 - (I.card : ℤ))
    (hj : j ∉ I) : f.component I k hI hk = 0 := by
  let J := I.preimage j.succAbove j.succAboveOrderEmb.injective.injOn
  have hcard : J.card = I.card := HornIndex.card_preimage I j hj
  have hJ : J.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact hI.card_pos)
  have hImage : J.image j.succAboveOrderEmb.toOrderHom = I := HornIndex.image_preimage I j hj
  have h := congrArg (fun z : LinearData A x y n =>
    z.component J k hJ (by rw [hcard]; exact hk)) hf
  rw [LinearData.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn] at h
  simp only [hImage] at h
  change f.component I k hI hk = 0 at h
  exact h

/-- 零の指定面を通る任意の単調写像による線形引き戻しは零。 -/
lemma pinchedLinearData_pullback_zero_of_avoids {m n : ℕ}
    (f : LinearData A x y (n + 1)) (j : Fin (n + 2))
    (hf : LinearData.pullback j.succAboveOrderEmb.toOrderHom f = 0)
    (α : Fin (m + 1) →o Fin (n + 2)) (hα : ∀ r, α r ≠ j) :
    LinearData.pullback α f = 0 := by
  funext i
  rcases i with ⟨⟨I, k⟩, hI, hk⟩
  change (LinearData.pullback α f).component I k hI hk = 0
  by_cases hi : Set.InjOn α (I : Set (Fin (m + 1)))
  · rw [LinearData.pullback_component_of_inj _ _ _ _ _ _ hi]
    apply pinchedLinearData_component_zero_of_face f j hf
    intro hj
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hj
    exact hα r hr
  · exact LinearData.pullback_component_of_not_inj α f I k hI hk hi

/-- 零の指定面を通る任意の実単体の引き戻しも零単体。 -/
lemma pinchedSimplex_pullback_zero_of_avoids {m : SimplexCategory} {d : ℕ}
    (f : LinearSimplex A x y (d + 1)) (j : Fin (d + 2))
    (hf : LinearSimplex.pullback j.succAboveOrderEmb.toOrderHom f = 0)
    (α : m ⟶ ⦋d + 1⦌) (hα : ∀ r, α.toOrderHom r ≠ j) :
    f.toPinched.pullback α = (0 : LinearSimplex A x y m.len).toPinched := by
  apply (linearEquiv x y m.len).injective
  change toLinearSimplex (f.toPinched.pullback α) =
    toLinearSimplex (0 : LinearSimplex A x y m.len).toPinched
  rw [toLinearSimplex_pullback, LinearSimplex.toLinearSimplex_toPinched,
    LinearSimplex.toLinearSimplex_toPinched]
  apply Subtype.ext
  exact pinchedLinearData_pullback_zero_of_avoids f.val j (congrArg Subtype.val hf)
    α.toOrderHom hα

end SerrePositivity.InfinityCategories
