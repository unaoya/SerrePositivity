module
public import SerrePositivity.KST.SConstruction.DGClosedIsoConjugation

/-! # 全 Hom 共役の恒等・合成・逆
概要：閉零同型による Hom 複体の共役が、同型の合成と厳密に両立する。
方針：前後合成の交換と中間射の相殺を、抽象豊穣圏で検証する。
規約：検証上限を変更しない。使われ方：ラベル付き Perf の作用の関手法則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable (V : Type u) [Category V] [MonoidalCategory V]
  {C : Type v} [Category C] [EnrichedOrdinaryCategory V C]

/-- 恒等同型による全 Hom 共役は恒等射。 -/
lemma enrichedClosedIsoConjugation_refl (X Y : C) :
    enrichedClosedIsoConjugation V (Iso.refl X) (Iso.refl Y) = 𝟙 _ := by
  simp only [enrichedClosedIsoConjugation, Iso.refl_inv, Iso.refl_hom,
    eHomWhiskerRight_id, eHomWhiskerLeft_id, Category.id_comp]

/-- 連続する二つの全 Hom 共役は、元の閉零同型の合成による共役。 -/
lemma enrichedClosedIsoConjugation_trans {X X' X'' Y Y' Y'' : C}
    (e : X ≅ X') (e' : X' ≅ X'') (f : Y ≅ Y') (f' : Y' ≅ Y'') :
    enrichedClosedIsoConjugation V e f ≫ enrichedClosedIsoConjugation V e' f' =
      enrichedClosedIsoConjugation V (e ≪≫ e') (f ≪≫ f') := by
  simp only [enrichedClosedIsoConjugation, Iso.trans_inv, Iso.trans_hom, Category.assoc]
  rw [eHom_whisker_exchange_assoc, ← eHomWhiskerRight_comp_assoc,
    ← eHomWhiskerLeft_comp]

/-- 元の実閉零同型の共役は、全 Hom 複体の実同型。 -/
def enrichedClosedIsoHomIso {X X' Y Y' : C} (e : X ≅ X') (f : Y ≅ Y') :
    (X ⟶[V] Y) ≅ (X' ⟶[V] Y') where
  hom := enrichedClosedIsoConjugation V e f
  inv := enrichedClosedIsoConjugation V e.symm f.symm
  hom_inv_id := by
    rw [enrichedClosedIsoConjugation_trans]
    simp [enrichedClosedIsoConjugation]
  inv_hom_id := by
    rw [enrichedClosedIsoConjugation_trans]
    simp [enrichedClosedIsoConjugation]

end SerrePositivity.KST.SConstruction
