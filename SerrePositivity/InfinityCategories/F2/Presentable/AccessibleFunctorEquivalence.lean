module

public import SerrePositivity.InfinityCategories.F2.Presentable.EquivalenceColimits

/-!
概要：accessible 関手の性質は、全自然同型と両側の同値による共役で不変。
方針：同じ κ の filtered 保存性を同値と逆同値で合成し、指定合成同型で元へ戻す。
規約：圏の濃度変更や正則性の存在を新たに仮定しない。同じ元の関手を回収する。
使われ方：accessible 圏間の関手の基本性質と後続の随伴関手定理。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 元の全関手同型で比較される関手は、accessibility を共有する。 -/
lemma IsAccessibleFunctor.of_functorIso {C E : SSet.{u + 1}} [Quasicategory E]
    {F G : C ⟶ E} (h : IsAccessibleFunctor F) (e : FunctorIso F G) : IsAccessibleFunctor G := by
  obtain ⟨κ, hκ, h⟩ := h
  exact ⟨κ, hκ, h.of_functorIso e⟩

/-- 同じ濃度の filtered 保存性は、両側の同値による元の関手の共役で不変。 -/
lemma isKappaAccessibleFunctor_iff_equivalence_conjugate (κ : Cardinal.{u})
    {A B C D : SSet.{u + 1}} [Quasicategory A] [Quasicategory B]
    [Quasicategory C] [Quasicategory D] (eC : QCatEquivalence A C)
    (eD : QCatEquivalence D B) (F : C ⟶ D) :
    IsKappaAccessibleFunctor κ F ↔
      IsKappaAccessibleFunctor κ (eC.hom ≫ F ≫ eD.hom) := by
  constructor
  · intro h
    exact (equivalence_preservesSmallKappaFilteredColimits κ eC.isQCatEquivalence).comp
      (h.comp (equivalence_preservesSmallKappaFilteredColimits κ eD.isQCatEquivalence))
  · intro h
    have hCi : IsKappaAccessibleFunctor κ eC.inv :=
      equivalence_preservesSmallKappaFilteredColimits κ eC.symm.isQCatEquivalence
    have hDi : IsKappaAccessibleFunctor κ eD.inv :=
      equivalence_preservesSmallKappaFilteredColimits κ eD.symm.isQCatEquivalence
    have h' := (hCi.comp h).comp hDi
    have e₀ : FunctorIso (eC.inv ≫ (eC.hom ≫ F ≫ eD.hom) ≫ eD.inv)
        (F ≫ eD.hom ≫ eD.inv) := by
      simpa only [Category.assoc, Category.id_comp] using
        eC.invHomIso.postcomp (F ≫ eD.hom ≫ eD.inv)
    have e₁ : FunctorIso (F ≫ eD.hom ≫ eD.inv) F := by
      simpa only [Category.assoc, Category.comp_id] using eD.homInvIso.precomp F
    apply h'.of_functorIso
    simpa only [Category.assoc] using e₀ ≪≫ e₁

/-- accessible 関手の性質は、両側の同値による共役で必要十分に保存される。 -/
lemma isAccessibleFunctor_iff_equivalence_conjugate
    {A B C D : SSet.{u + 1}} [Quasicategory A] [Quasicategory B]
    [Quasicategory C] [Quasicategory D] (eC : QCatEquivalence A C)
    (eD : QCatEquivalence D B) (F : C ⟶ D) :
    IsAccessibleFunctor F ↔ IsAccessibleFunctor (eC.hom ≫ F ≫ eD.hom) := by
  constructor
  · rintro ⟨κ, hκ, h⟩
    exact ⟨κ, hκ, (isKappaAccessibleFunctor_iff_equivalence_conjugate κ eC eD F).mp h⟩
  · rintro ⟨κ, hκ, h⟩
    exact ⟨κ, hκ, (isKappaAccessibleFunctor_iff_equivalence_conjugate κ eC eD F).mpr h⟩

end SerrePositivity.InfinityCategories.F2.Presentable
