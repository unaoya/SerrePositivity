module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FiberTriangle

/-! # 標準 fiber と mapping cocone の座標

概要：標準 fiber のホモトピーを cocone の第二射影と照合し、二射影による射の外延性を与える。
方針：シフト cochain の成分と cocone の直和分解を使う。
規約：全整数次数、非有界複体。使われ方：D7 の比較写像の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable {S : Type u} [CommRing S] {A B X : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 標準 fiber の零ホモトピーは mapping cocone の第二射影の負。 -/
lemma fiberNullHomotopy_eq_neg_mappingCocone_snd (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberNullHomotopy f = -(mappingCocone.snd f) := by
  apply Cochain.ext
  intro p q hpq
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberNullHomotopy, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberShiftCocycle, Cocycle.equivHomShift_apply,
    Cochain.rightUnshift_v, mappingCocone.snd,
    Cochain.leftShift_v, Cochain.ofHom_v, sub_eq_add_neg, Int.negOnePow_even 2 ⟨1, rfl⟩]

/-- Mapping cocone の第一射影の各次数は cone の第一射影の成分。 -/
lemma mappingCocone_fst_f (f : A ⟶ B) (p : ℤ) :
    (mappingCocone.fst f).f p = (mappingCone.fst f).val.v (p - 1) p (by omega) := by
  simp only [mappingCocone.fst, HomologicalComplex.neg_f_apply, Cocycle.homOf_f,
    Cocycle.leftShift_coe]
  rw [Cochain.leftShift_v _ (-1) 0 (add_neg_cancel 1) p p (add_zero p) (p - 1) (by omega)]
  norm_num [CochainComplex.shiftFunctorObjXIso, sub_eq_add_neg]
  exact Category.id_comp _

/-- Mapping cocone の第二射影の各次数は cone の第二射影の成分。 -/
lemma mappingCocone_snd_v (f : A ⟶ B) (p : ℤ) :
    (mappingCocone.snd f).v p (p - 1) (by omega) =
      (mappingCone.snd f).v (p - 1) (p - 1) (add_zero (p - 1)) := by
  rw [mappingCocone.snd,
    Cochain.leftShift_v _ (-1) (-1) (zero_add (-1)) p (p - 1) (by omega) (p - 1) (add_zero _)]
  norm_num [CochainComplex.shiftFunctorObjXIso, sub_eq_add_neg,
    Int.negOnePow_even 2 ⟨1, rfl⟩]
  exact Category.id_comp _

/-- Mapping cocone への射は第一射影と第二射影の成分で定まる。 -/
lemma mappingCocone_hom_ext (f : A ⟶ B) {a b : X ⟶ mappingCocone f}
    (h₁ : a ≫ mappingCocone.fst f = b ≫ mappingCocone.fst f)
    (h₂ : ∀ p q hpq, a.f p ≫ (mappingCocone.snd f).v p q hpq =
      b.f p ≫ (mappingCocone.snd f).v p q hpq) : a = b := by
  apply HomologicalComplex.hom_ext
  intro p
  have hfst := congrArg (fun z => z.f p) h₁
  change a.f p ≫ (mappingCocone.fst f).f p = b.f p ≫ (mappingCocone.fst f).f p at hfst
  calc
    a.f p = a.f p ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = a.f p ≫ ((mappingCocone.fst f).f p ≫ (mappingCocone.inl f).v p p (add_zero p) +
        (mappingCocone.snd f).v p (p - 1) (by omega) ≫
          (mappingCocone.inr f).val.v (p - 1) p (by omega)) := by
      rw [mappingCocone.id_X]
    _ = b.f p ≫ ((mappingCocone.fst f).f p ≫ (mappingCocone.inl f).v p p (add_zero p) +
        (mappingCocone.snd f).v p (p - 1) (by omega) ≫
          (mappingCocone.inr f).val.v (p - 1) p (by omega)) := by
      rw [Preadditive.comp_add, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
        ← Category.assoc, ← Category.assoc, hfst, h₂]
    _ = b.f p := by rw [mappingCocone.id_X, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
