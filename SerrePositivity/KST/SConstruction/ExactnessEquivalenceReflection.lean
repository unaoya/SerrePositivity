module
public import SerrePositivity.InfinityCategories.Stable.EquivalenceStability
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorChoice

/-! # 評価同値による完全性の反映
概要：実 ∞ 圏同値との前後合成は、零対象と cofiber 列の保存を保ち反映する。
方針：同値の逆も完全であることと、元の二つの関手同型を使う。
規約：安定性や対象の Small 仮定を追加しない。使われ方：ラベル付き Perf の射の完全性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet SerrePositivity.InfinityCategories
variable {X Y Z : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory Z]

/-- 値域の実同値との合成は、元の射の完全性を保ち反映する。 -/
lemma isExactFunctor_comp_equivalence_iff (F : X ⟶ Y) (e : QCatEquivalence Y Z) :
    IsExactFunctor (F ≫ e.hom) ↔ IsExactFunctor F := by
  have : IsExactFunctor e.hom := isExactFunctor_of_isQCatEquivalence e.isQCatEquivalence
  have : IsExactFunctor e.inv := isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  constructor
  · intro h
    let := h
    have he : FunctorIso ((F ≫ e.hom) ≫ e.inv) F := by
      simpa only [Category.assoc, Category.comp_id] using e.homInvIso.precomp F
    exact isExactFunctor_of_functorIso he
  · intro h
    let := h
    infer_instance

/-- 始域の実同値との合成も、元の射の完全性を保ち反映する。 -/
lemma isExactFunctor_equivalence_comp_iff (e : QCatEquivalence X Y) (F : Y ⟶ Z) :
    IsExactFunctor (e.hom ≫ F) ↔ IsExactFunctor F := by
  have : IsExactFunctor e.hom := isExactFunctor_of_isQCatEquivalence e.isQCatEquivalence
  have : IsExactFunctor e.inv := isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  constructor
  · intro h
    let := h
    have he : FunctorIso (e.inv ≫ (e.hom ≫ F)) F := by
      simpa only [Category.assoc, Category.id_comp] using e.invHomIso.postcomp F
    exact isExactFunctor_of_functorIso he
  · intro h
    let := h
    infer_instance

end SerrePositivity.KST.SConstruction
