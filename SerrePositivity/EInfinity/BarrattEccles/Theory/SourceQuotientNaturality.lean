module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.InducedQuotientCompatibility

/-!
# 入力側の指定全複体商の自然性

HA 3.2.4.7 の自由比較で、群変更と入力射に沿って指定商を保つための補助。
BS-W16 の型一覧 L01〜L03 に対応する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable {R G H : Type u} [CommRing R] [Group G] [Group H]
variable {K K' L : Complex R}

/-- 指定全複体商は、群の同型による変更で保たれる。 -/
lemma coinvariantTotalGroupChangeIso_quotient
    (e : H ≃* G) (ρ : G →* End K) (σ : G →* End L) :
    coinvariantTotalQuotient (ρ.comp e.toMonoidHom) (σ.comp e.toMonoidHom) ≫
      (coinvariantTotalGroupChangeIso e ρ σ).hom = coinvariantTotalQuotient ρ σ := by
  apply (cancel_mono (coinvariantTensorTotalIso ρ σ).hom).1
  simp only [coinvariantTotalGroupChangeIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, coinvariantTotalQuotient_comparison,
    coinvariantTotalQuotient_comparison]
  exact coinvariantGroupChangeComplexIso_quotient (tensorComplexAction ρ σ) e

/-- 指定全複体商は、係数を固定した同変な入力射と可換する。 -/
lemma coinvariantTotalQuotient_naturality_left
    (ρ : G →* End K) (τ : G →* End K') (σ : G →* End L)
    (f : K ⟶ K') (hf : ∀ g, (ρ g).asHom ≫ f = f ≫ (τ g).asHom) :
    coinvariantTotalQuotient ρ σ ≫
      (inputCoinvariantTotalFunctor (representationCochainComplex σ)).map
        (representationCochainMap ρ τ f hf) =
    (f ▷ L) ≫ coinvariantTotalQuotient τ σ := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply mapBifunctor.hom_ext
  intro i j h
  change ιMapBifunctor K L (curriedTensor (ModuleCat R)) (.up ℤ) i j k h ≫
    (coinvariantTotalQuotient ρ σ ≫ mapBifunctorMap (representationCochainMap ρ τ f hf)
      (𝟙 (representationCochainComplex σ)) (Rep.coinvariantsTensor R G) (.up ℤ)).f k =
    ιMapBifunctor K L (curriedTensor (ModuleCat R)) (.up ℤ) i j k h ≫
      (mapBifunctorMap f (𝟙 L) (curriedTensor (ModuleCat R)) (.up ℤ) ≫
        coinvariantTotalQuotient τ σ).f k
  rw [HomologicalComplex.comp_f, ← Category.assoc, coinvariantTotalQuotient_ι,
    Category.assoc, ι_mapBifunctorMap]
  rw [HomologicalComplex.comp_f, ι_mapBifunctorMap_assoc, coinvariantTotalQuotient_ι]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

/-- 入力作用の等式による運搬は、指定全複体商を保つ。 -/
lemma coinvariantTotalQuotient_transport_left
    (ρ τ : G →* End K) (σ : G →* End L) (h : ρ = τ) :
    coinvariantTotalQuotient ρ σ ≫
      (inputCoinvariantTotalFunctor (representationCochainComplex σ)).map
        (eqToIso (congrArg representationCochainComplex h)).hom =
    coinvariantTotalQuotient τ σ := by
  subst τ
  simp only [eqToIso.hom, eqToHom_refl]
  let F := inputCoinvariantTotalFunctor (representationCochainComplex σ)
  exact (congrArg (fun q => coinvariantTotalQuotient ρ σ ≫ q)
    (F.map_id (representationCochainComplex ρ))).trans
      (Category.comp_id (coinvariantTotalQuotient ρ σ))

end SerrePositivity.EInfinity
