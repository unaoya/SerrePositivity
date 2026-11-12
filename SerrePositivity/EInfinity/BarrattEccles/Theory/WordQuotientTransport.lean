module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.OrbitQuotientCompatibility

/-!
# 等しい入力語に沿う指定商の運搬

HA 3.2.4.7 の自由比較で、同じ語の二つの表示を指定商とともに同定する。
BS-W16 の追加照合 I1。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory HomologicalComplex MonoidalCategory
open SerrePositivity.DifferentialGraded
variable {R G : Type u} [CommRing R] [Group G]

/-- 語の等式から作った同型は、同じ指定全複体商を保つ。 -/
lemma coinvariantTotalQuotient_wordCongr (X Y : Complex R) {L : Complex R}
    {r : ℕ} {w z : BinaryTensorWord r} (h : w = z)
    (φ : G →* Equiv.Perm (Fin r)) (hw : ∀ g, φ g • w = w)
    (hz : ∀ g, φ g • z = z) (σ : G →* End L) :
    coinvariantTotalQuotient (binaryTensorWordFixedAction X Y r w φ hw) σ ≫
      (inputCoinvariantTotalFunctor (representationCochainComplex σ)).map
        (binaryTensorFixedRepresentationCongr X Y h φ hw hz).hom =
    (eqToHom (congrArg (binaryTensorWordObj X Y r) h) ▷ L) ≫
      coinvariantTotalQuotient (binaryTensorWordFixedAction X Y r z φ hz) σ := by
  subst z
  simp only [binaryTensorFixedRepresentationCongr, Iso.refl_hom, eqToHom_refl,
    id_whiskerRight, Category.id_comp]
  let F := inputCoinvariantTotalFunctor (representationCochainComplex σ)
  exact (congrArg (fun f =>
    coinvariantTotalQuotient (binaryTensorWordFixedAction X Y r w φ hw) σ ≫ f)
    (F.map_id (binaryTensorWordFixedRepresentation X Y r w φ hw))).trans
      (Category.comp_id _)

end SerrePositivity.EInfinity
