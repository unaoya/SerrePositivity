module

public import SerrePositivity.CategoryTheory.Monoidal.PowerBijectionAppend
public import SerrePositivity.Spectra.SymmetricSequence.SumMonoidal

/-! # 有限全単射圏上の反復テンソルのモノイダル関手

既存の連結同型・第0段と、証明済みの自然性・結合・単位の整合性を
Mathlibのモノイダル関手の構造へまとめる。braidingの保存は別に証明する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory SerrePositivity.FiniteBijection

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

private lemma finCongr_trans_eq {a b c : ℕ} (h : a = b) (k : b = c) :
    (finCongr h).trans (finCongr k) = finCongr (h.trans k) := by
  subst b
  subst c
  rfl
/-- 添字圏の結合子の像は、次数の結合則による移送。 -/
lemma bijectionFunctor_map_associator (X : C) (A B D : FiniteBijection) :
    (bijectionFunctor X).map (sumAssociator A B D).hom =
      eqToHom (congrArg (power X) (Nat.add_assoc (card A) (card B) (card D))) := by
  simp [bijectionFunctor, familyFunctor, familyMap, sumAssociator, isoOfEquiv,
    assocEquiv_eq_finCongr, finCongr_trans_eq, ← Equiv.Perm.one_def]
/-- 添字圏の左単位子の像は、次数の移送。 -/
lemma bijectionFunctor_map_leftUnitor (X : C) (A : FiniteBijection) :
    (bijectionFunctor X).map (sumLeftUnitor A).hom =
      eqToHom (congrArg (power X) (Nat.zero_add (card A))) := by
  simp [bijectionFunctor, familyFunctor, familyMap, sumLeftUnitor, isoOfEquiv,
    finCongr_trans_eq, ← Equiv.Perm.one_def]
/-- 添字圏の右単位子の像は恒等射。 -/
lemma bijectionFunctor_map_rightUnitor (X : C) (A : FiniteBijection) :
    (bijectionFunctor X).map (sumRightUnitor A).hom = 𝟙 (power X (card A)) := by
  simp [bijectionFunctor, familyFunctor, familyMap, sumRightUnitor, isoOfEquiv]
  rfl
/-- 既存の連結同型と第0段から得るモノイダル関手のデータ。 -/
def bijectionFunctorCoreMonoidal (X : C) : (bijectionFunctor X).CoreMonoidal where
  εIso := Iso.refl _
  μIso A B := appendIso X (card A) (card B)
  μIso_hom_natural_left {A A'} f B := by
    have h := (appendNatTrans X).naturality (X := (A,B)) (Y := (A',B)) (f, 𝟙 B)
    simpa only [externalProductBifunctor_obj_map, CategoryTheory.Functor.map_id,
      tensorHom_id, whiskerLeft_id, Category.comp_id, CategoryTheory.Functor.comp_map,
      appendNatTrans_app, externalProductBifunctor_obj_obj, CategoryTheory.Functor.comp_obj,
      sumFunctor, tensorObj_eq_sumObj, whiskerRight_eq_sumMap,
      whiskerLeft_eq_sumMap] using h
  μIso_hom_natural_right {A A'} B f := by
    have h := (appendNatTrans X).naturality (X := (B,A)) (Y := (B,A')) (𝟙 B, f)
    simpa only [externalProductBifunctor_obj_map, CategoryTheory.Functor.map_id,
      id_tensorHom, id_whiskerRight, Category.id_comp, CategoryTheory.Functor.comp_map,
      appendNatTrans_app, externalProductBifunctor_obj_obj, CategoryTheory.Functor.comp_obj,
      sumFunctor, tensorObj_eq_sumObj, whiskerRight_eq_sumMap,
      whiskerLeft_eq_sumMap] using h
  associativity A B D := by
    erw [bijectionFunctor_map_associator]
    exact appendIso_associativity X (card A) (card B) (card D)
  left_unitality A := by
    simp only [Iso.refl_hom, id_whiskerRight, Category.id_comp]
    erw [bijectionFunctor_map_leftUnitor, appendIso_zero_left]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rfl
  right_unitality A := by
    simp only [Iso.refl_hom, whiskerLeft_id, Category.id_comp]
    erw [bijectionFunctor_map_rightUnitor, appendIso_zero_right]
    erw [Category.comp_id]
    rfl

/-- 反復テンソル関手を、既存の連結同型を持つモノイダル関手として登録する。 -/
instance bijectionFunctorMonoidal (X : C) : (bijectionFunctor X).Monoidal :=
  (bijectionFunctorCoreMonoidal X).toMonoidal

/-- 登録したtensoratorは既存の連結同型の射。 -/
lemma bijectionFunctor_μ (X : C) (A B : FiniteBijection) :
    Functor.LaxMonoidal.μ (bijectionFunctor X) A B = (appendIso X (card A) (card B)).hom := rfl

/-- 登録した逆tensoratorは既存の連結同型の逆射。 -/
lemma bijectionFunctor_δ (X : C) (A B : FiniteBijection) :
    Functor.OplaxMonoidal.δ (bijectionFunctor X) A B = (appendIso X (card A) (card B)).inv := rfl

end SerrePositivity.TensorPowers
