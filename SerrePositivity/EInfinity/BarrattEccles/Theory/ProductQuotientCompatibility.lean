module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.FreeCoefficientCompatibility

/-!
# 直積群の分離と指定商写像

HA 3.2.4.7 の自由比較のため、余不変の分離を元の複体の射として照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable {A G H : Type u} [CommRing A] [Group G] [Group H]
  {K L : Complex A} (ρ : G →* End K) (σ : H →* End L)

/-- 元の作用を持つ複体から指定された余不変への商写像。 -/
def actionCoinvariantQuotient : K ⟶ actionCoinvariantComplex ρ :=
  (representationCochainForgetIso ρ).inv ≫
    (NatTrans.mapHomologicalComplex (Rep.coinvariantsMk A G) (.up ℤ)).app
      (representationCochainComplex ρ)

/-- 同変な複体の射は、元の指定商写像と厳密に可換する。 -/
lemma actionCoinvariantQuotient_naturality (τ : G →* End L) (f : K ⟶ L)
    (hf : ∀ g, (ρ g).asHom ≫ f = f ≫ (τ g).asHom) :
    actionCoinvariantQuotient ρ ≫
      ((Rep.coinvariantsFunctor A G).mapHomologicalComplex (.up ℤ)).map
        (representationCochainMap ρ τ f hf) = f ≫ actionCoinvariantQuotient τ := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  rfl

/-- 同じ作用の等式に沿う表示の運搬は、元の指定商写像を保つ。 -/
lemma actionCoinvariantQuotient_transport (τ : G →* End K) (h : ρ = τ) :
    actionCoinvariantQuotient ρ ≫
      (((Rep.coinvariantsFunctor A G).mapHomologicalComplex (.up ℤ)).mapIso
        (eqToIso (congrArg representationCochainComplex h))).hom =
          actionCoinvariantQuotient τ := by
  subst τ
  simp only [Functor.mapIso_hom, eqToIso.hom, eqToHom_refl]
  let F := (Rep.coinvariantsFunctor A G).mapHomologicalComplex (.up ℤ)
  exact (congrArg (fun q => actionCoinvariantQuotient ρ ≫ q)
    (F.map_id (representationCochainComplex ρ))).trans
      (Category.comp_id (actionCoinvariantQuotient ρ))

/-- 直積群の全複体の分離は、左右の指定商写像のテンソルを保つ。 -/
lemma productCoinvariantTotalIso_quotient :
    coinvariantTotalQuotient (ρ.comp (MonoidHom.fst G H))
      (σ.comp (MonoidHom.snd G H)) ≫ (productCoinvariantTotalIso ρ σ).hom =
    actionCoinvariantQuotient ρ ⊗ₘ actionCoinvariantQuotient σ := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply mapBifunctor.hom_ext
  intro i j h
  rw [HomologicalComplex.comp_f, ← Category.assoc, coinvariantTotalQuotient_ι]
  simp only [Category.assoc, productCoinvariantTotalIso, HomologicalComplex₂.total.mapIso,
    ιMapBifunctor]
  rw [HomologicalComplex₂.ιTotal_map]
  simp only [actionCoinvariantQuotient]
  change _ = ιMapBifunctor K L (curriedTensor (ModuleCat A)) (.up ℤ) i j k h ≫
    (mapBifunctorMap (actionCoinvariantQuotient ρ) (actionCoinvariantQuotient σ)
      (curriedTensor (ModuleCat A)) (.up ℤ)).f k
  rw [ι_mapBifunctorMap]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  rfl

/-- 群の同型による変更は、元の作用の指定商写像を保つ。 -/
lemma coinvariantGroupChangeComplexIso_quotient (e : H ≃* G) :
    actionCoinvariantQuotient (ρ.comp e.toMonoidHom) ≫
      (coinvariantGroupChangeComplexIso e (representationCochainComplex ρ)).hom =
        actionCoinvariantQuotient ρ := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  rfl

/-- テンソル複体の実際の対角作用の商を、左右の指定商へ分離する。 -/
lemma productCoinvariantComplexIso_quotient :
    actionCoinvariantQuotient (tensorComplexAction (ρ.comp (MonoidHom.fst G H))
      (σ.comp (MonoidHom.snd G H))) ≫ (productCoinvariantComplexIso ρ σ).hom =
        actionCoinvariantQuotient ρ ⊗ₘ actionCoinvariantQuotient σ := by
  simpa only [actionCoinvariantQuotient, productCoinvariantComplexIso,
    coinvariantTotalQuotient, Iso.trans_hom, Iso.symm_hom, Category.assoc] using
      productCoinvariantTotalIso_quotient ρ σ

end SerrePositivity.EInfinity
