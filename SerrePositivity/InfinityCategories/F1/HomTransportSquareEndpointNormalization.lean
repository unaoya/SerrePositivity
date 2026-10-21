module

public import SerrePositivity.InfinityCategories.F1.HomTransportSquareIdentity
public import SerrePositivity.InfinityCategories.F1.FunctorIsoPrecompositionCoherence
public import SerrePositivity.InfinityCategories.F1.FunctorIsoEndpointProjection

/-!
概要：厳密な輸送正方形の等号同型を、同じ指定比較の端点正規化として回収する。
方針：等号の同型の前後合成を計算し、同じ両端の等式を消去する。
規約：元の正方形と指定同型の値を保持する。
使われ方：第一辺の制限正方形を局所自然性と同じ端点へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 等号による指定同型の後合成は、同じ合成した射の等号による同型。 -/
lemma FunctorIso.postcomp_eqToIso {A E B : SSet.{u}} {f g : A ⟶ E}
    (h : f = g) (p : E ⟶ B) :
    FunctorIso.postcomp (eqToIso (congrArg
      (fun v ↦ SSet.HomotopyCategory.mk (functorVertex v)) h)) p =
      eqToIso (congrArg (fun v ↦ SSet.HomotopyCategory.mk (functorVertex (v ≫ p))) h) := by
  subst g
  apply Iso.ext
  rw [F2.functorIso_postcomp_hom]
  simp only [eqToIso_refl, Iso.refl_hom, CategoryTheory.Functor.map_id]
  rfl

/-- 指定正方形の等号同型は、同じ比較の両端を正規化すると消去される。 -/
lemma functorIso_eqToIso_square_cancel {A E : SSet.{u}} {a b b' c c' : A ⟶ E}
    (hb : b = b') (hc : c = c') (e : FunctorIso a b) (d : FunctorIso b' c')
    (n : FunctorIso a c)
    (h : e ≪≫ eqToIso (congrArg
        (fun v ↦ SSet.HomotopyCategory.mk (functorVertex v)) hb) ≪≫ d =
      n ≪≫ eqToIso (congrArg
        (fun v ↦ SSet.HomotopyCategory.mk (functorVertex v)) hc)) :
    e ≪≫ F2.functorIsoOfEq d hb.symm hc.symm = n := by
  subst b' c'
  simpa only [F2.functorIsoOfEq, eqToIso_refl, Iso.refl_trans, Iso.trans_refl] using h

/-- 厳密な span の射による元の輸送正方形は、同じ端点へ正規化した指定比較で可換。 -/
lemma HomTransportSquareCommutes.strict_normalized
    {H₀ H₁ X₀ X₁ Y₀ Y₁ : SSet.{u}}
    (p₀ : H₀ ⟶ X₀) (p₁ : H₀ ⟶ X₁) (q₀ : H₁ ⟶ Y₀) (q₁ : H₁ ⟶ Y₁) (r : H₀ ⟶ H₁)
    (t₀ : X₁ ⟶ X₀) (t₁ : Y₁ ⟶ Y₀) (u₀ : X₀ ⟶ Y₀) (u₁ : X₁ ⟶ Y₁)
    (e₀ : FunctorIso (p₁ ≫ t₀) p₀) (e₁ : FunctorIso (q₁ ≫ t₁) q₀)
    (e : FunctorIso (t₀ ≫ u₀) (u₁ ≫ t₁))
    (h₀ : p₀ ≫ u₀ = r ≫ q₀) (h₁ : p₁ ≫ u₁ = r ≫ q₁)
    (hs : r ≫ (q₁ ≫ t₁) = (p₁ ≫ u₁) ≫ t₁)
    (h : HomTransportSquareCommutes p₀ p₁ q₀ q₁ r t₀ t₁ u₀ u₁ e₀ e₁
      (eqToIso (congrArg (fun v ↦ SSet.HomotopyCategory.mk (functorVertex v)) h₀))
      (eqToIso (congrArg (fun v ↦ SSet.HomotopyCategory.mk (functorVertex v)) h₁)) e) :
    e.precomp p₁ ≪≫ F2.functorIsoOfEq (e₁.precomp r) hs h₀.symm = e₀.postcomp u₀ := by
  unfold HomTransportSquareCommutes at h
  rw [FunctorIso.postcomp_eqToIso h₁ t₁] at h
  exact functorIso_eqToIso_square_cancel hs.symm h₀ _ _ _ h

end SerrePositivity.InfinityCategories
