module

public import SerrePositivity.InfinityCategories.Kan.PosetMaximalCover
public import SerrePositivity.InfinityCategories.Stable.PosetSubtypeNerve
public import SerrePositivity.InfinityCategories.Stable.FinitePosetNerve

/-!
概要：極大点の除去部分と弱下方部分の元の順序部分型 nerve は実 pushout を与える。
方針：供給された部分型比較で、全部分複体の pushout を元の順序包含へ移す。
規約：Stable の供給はコーディネータ許可による読み取り専用 import。
使われ方：Ind の固定下方部分を保つ有限半順序帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：極大点追加は元の順序部分型包含の pushout。
方針：全部分複体比較。規約：元の全包含。使われ方：点追加の図式貼り合わせ。 -/
lemma posetNerve_maximal_subtype_isPushout {P : Type u} [PartialOrder P]
    (a : P) (ha : IsMax a) :
    IsPushout
      (nerveMap (⟨fun p ↦ ⟨p.val, p.property.ne⟩, fun _ _ h ↦ h⟩ :
        {p : P // p < a} →o {p : P // p ≠ a}).toFunctor)
      (nerveMap (⟨fun p ↦ ⟨p.val, p.property.le⟩, fun _ _ h ↦ h⟩ :
        {p : P // p < a} →o {p : P // p ≤ a}).toFunctor)
      (nerveMap (posetSubtypeInclusion (fun p : P ↦ p ≠ a)))
      (nerveMap (posetSubtypeInclusion (fun p : P ↦ p ≤ a))) := by
  apply (posetNerve_maximal_isPushout a ha).of_iso'
    (posetSubtypeNerveIso (fun p : P ↦ p < a))
    (posetSubtypeNerveIso (fun p : P ↦ p ≠ a))
    (posetSubtypeNerveIso (fun p : P ↦ p ≤ a)) (Iso.refl _)
  · apply (cancel_mono
      (fullSubcomplexOnVertices (nerve P) (fun v ↦ nerveEquiv v ≠ a)).ι).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι, posetSubtypeNerveIso_hom_ι]
    rfl
  · apply (cancel_mono
      (fullSubcomplexOnVertices (nerve P) (fun v ↦ nerveEquiv v ≤ a)).ι).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι, posetSubtypeNerveIso_hom_ι]
    rfl
  · simpa only [Iso.refl_hom, Category.comp_id] using
      posetSubtypeNerveIso_hom_ι (fun p : P ↦ p ≠ a)
  · simpa only [Iso.refl_hom, Category.comp_id] using
      posetSubtypeNerveIso_hom_ι (fun p : P ↦ p ≤ a)

end SerrePositivity.InfinityCategories.F2.Ind
