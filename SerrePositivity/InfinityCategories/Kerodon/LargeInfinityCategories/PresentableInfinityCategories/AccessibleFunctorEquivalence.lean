module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.EquivalenceColimits

/-!
概要：accessible 関手の性質は、全自然同型と両側の同値による共役で不変。
方針：同じ κ の filtered 保存性を同値と逆同値で合成し、指定合成同型で元へ戻す。
規約：圏の濃度変更や正則性の存在を新たに仮定しない。同じ元の関手を回収する。
使われ方：accessible 圏間の関手の基本性質と後続の随伴関手定理。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 元の全関手同型で比較される関手は、accessibility を共有する。 -/
lemma IsAccessibleFunctor.of_functorIso {C E : SSet.{u + 1}} [Quasicategory E]
    {F G : C ⟶ E} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor F) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor G := by
  obtain ⟨κ, hκ, h⟩ := h
  exact ⟨κ, hκ, h.of_functorIso e⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsAccessibleFunctor (of_functorIso)


/-- 同じ濃度の filtered 保存性は、両側の同値による元の関手の共役で不変。 -/
lemma isKappaAccessibleFunctor_iff_equivalence_conjugate (κ : Cardinal.{u})
    {A B C D : SSet.{u + 1}} [Quasicategory A] [Quasicategory B]
    [Quasicategory C] [Quasicategory D] (eC : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence A C)
    (eD : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence D B) (F : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ F ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (eC.hom ≫ F ≫ eD.hom) := by
  constructor
  · intro h
    exact (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits κ eC.isQCatEquivalence).comp
      (h.comp (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits κ eD.isQCatEquivalence))
  · intro h
    have hCi : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ eC.inv :=
      _root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits κ eC.symm.isQCatEquivalence
    have hDi : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ eD.inv :=
      _root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits κ eD.symm.isQCatEquivalence
    have h' := (hCi.comp h).comp hDi
    have e₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (eC.inv ≫ (eC.hom ≫ F ≫ eD.hom) ≫ eD.inv)
        (F ≫ eD.hom ≫ eD.inv) := by
      simpa only [Category.assoc, Category.id_comp] using
        eC.invHomIso.postcomp (F ≫ eD.hom ≫ eD.inv)
    have e₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ eD.hom ≫ eD.inv) F := by
      simpa only [Category.assoc, Category.comp_id] using eD.homInvIso.precomp F
    apply h'.of_functorIso
    simpa only [Category.assoc] using e₀ ≪≫ e₁

/-- accessible 関手の性質は、両側の同値による共役で必要十分に保存される。 -/
lemma isAccessibleFunctor_iff_equivalence_conjugate
    {A B C D : SSet.{u + 1}} [Quasicategory A] [Quasicategory B]
    [Quasicategory C] [Quasicategory D] (eC : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence A C)
    (eD : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence D B) (F : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor (eC.hom ≫ F ≫ eD.hom) := by
  constructor
  · rintro ⟨κ, hκ, h⟩
    exact ⟨κ, hκ, (isKappaAccessibleFunctor_iff_equivalence_conjugate κ eC eD F).mp h⟩
  · rintro ⟨κ, hκ, h⟩
    exact ⟨κ, hκ, (isKappaAccessibleFunctor_iff_equivalence_conjugate κ eC eD F).mpr h⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.5.1.2" (partial := direction) "仮定：accessible C と accessible D への反映 f⊣g、および元の L≃g∘f（HTT の (2) と一致）。結論：f は余極限を保存する左随伴として、g は右随伴として accessible で、その同じ合成 L も accessible（(2)⇒(3) に一致）。L の accessibility だけから像の accessibility を得る逆方向は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsAccessibleFunctor.of_functorIso
