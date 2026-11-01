module

public import SerrePositivity.CategoryTheory.Triangulated.VerdierLift
public import SerrePositivity.CategoryTheory.Karoubi.Basic
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Unique
public import SerrePositivity.DifferentialGraded.Derived.Coproducts
public import SerrePositivity.DifferentialGraded.Module.Colimits
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Filtration
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import SerrePositivity.CategoryTheory.Triangulated.VerdierKaroubi
public import SerrePositivity.DifferentialGraded.Module.HomotopyEvaluationTriangles
public import SerrePositivity.DifferentialGraded.Perfect.Compact.FiniteGeneration
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction
public import SerrePositivity.DifferentialGraded.Module.Isomorphism
public import SerrePositivity.DifferentialGraded.Derived.RestrictionTriangles
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionTriangles

/-!
# Verdier.Derived

## 概要
14 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## ShiftReflection（旧 SerrePositivity/DifferentialGraded/Verdier/ShiftReflection.lean） -/

/-! # 忠実な前合成による比較自然変換の shift 整合性の反映 -/

@[expose] public section ShiftReflection

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor
variable {M : Type*} [AddMonoid M] {B C D : Type*}
  [Category* B] [Category* C] [Category* D]
  [HasShift B M] [HasShift C M] [HasShift D M]
  (L : B ⥤ C) [L.CommShift M]
  [((whiskeringLeft B C D).obj L).Faithful]
  {F G : C ⥤ D} [F.CommShift M] [G.CommShift M] (τ : F ⟶ G)

/-- 前合成した比較が shift と可換なら、元の比較も同じ shift 構造と可換する。 -/
lemma natTransCommShift_of_precomp
    (hτ : NatTrans.CommShift (whiskerLeft L τ) M := by infer_instance) :
    NatTrans.CommShift τ M where
  shift_comm n := by
    let := hτ
    apply ((whiskeringLeft B C D).obj L).map_injective
    apply NatTrans.ext
    funext X
    apply (cancel_epi (F.map ((L.commShiftIso n).hom.app X))).1
    have h := NatTrans.shift_app_comm (whiskerLeft L τ) n X
    simp only [Functor.commShiftIso_comp_hom_app, whiskerLeft_app, Category.assoc] at h
    simpa only [Functor.whiskeringLeft_obj_map, whiskerLeft_app, NatTrans.comp_app,
      whiskerRight_app, Category.assoc, ← NatTrans.naturality_assoc] using h
end SerrePositivity.DifferentialGraded
end

end ShiftReflection

/-! ## KaroubiTransport（旧 SerrePositivity/DifferentialGraded/Verdier/KaroubiTransport.lean） -/

/-! # 圏同値を Karoubi 完備化へ運ぶ

既存の Karoubi 関手延長と retract による本質像判定を使う。
-/

@[expose] public section KaroubiTransport
universe u₁ u₂ v₁ v₂

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Idempotents
variable {C : Type u₁} [Category.{v₁} C] {T : Type u₂} [Category.{v₂} T]

lemma karoubiTransport_essSurj (e : C ≌ T) :
    ((functorExtension₂ C T).obj e.functor).EssSurj := by
  refine ⟨fun P => ?_⟩
  let X := e.functor.objPreimage P.X
  exact karoubiExtension_mem_essImage e.functor P X
    ((karoubiRetract P).trans (Retract.ofIso
      ((toKaroubi T).mapIso (e.functor.objObjPreimageIso P.X)).symm))

/-- 同値を既存の Karoubi 関手延長で完備化した同値。 -/
def karoubiEquivalenceTransport (e : C ≌ T) : Karoubi C ≌ Karoubi T := by
  let : ((functorExtension₂ C T).obj e.functor).EssSurj := karoubiTransport_essSurj e
  let : ((functorExtension₂ C T).obj e.functor).IsEquivalence := {}
  exact ((functorExtension₂ C T).obj e.functor).asEquivalence

end SerrePositivity.DifferentialGraded
end

end KaroubiTransport

/-! ## ShiftedHomComparison（旧 SerrePositivity/DifferentialGraded/Verdier/ShiftedHomComparison.lean） -/

/-! # 関手の Hom 写像の全単射性の同型・整数 shift による移送 -/

@[expose] public section ShiftedHomComparison
universe u₁ u₂ v₁ v₂

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] {T : Type u₂} [Category.{v₂} T] (F : C ⥤ T)

lemma homComparison_bijective_of_iso {X Y X' Y' : C} (e : X ≅ X') (d : Y ≅ Y')
    (h : Function.Bijective (F.map (X := X) (Y := Y))) :
    Function.Bijective (F.map (X := X') (Y := Y')) := by
  have hc : Function.Bijective (fun f : X ⟶ Y => F.map (Iso.homCongr e d f)) := by
    simpa only [Functor.map_homCongr, Function.comp_def] using
      (Iso.homCongr (F.mapIso e) (F.mapIso d)).bijective.comp h
  exact (Function.Bijective.of_comp_iff _ (Iso.homCongr e d).bijective).1 hc

variable [HasShift C ℤ] [HasShift T ℤ] [F.CommShift ℤ]

lemma homComparison_bijective_shift_both {X Y : C}
    (h : Function.Bijective (F.map (X := X) (Y := Y))) (n : ℤ) :
    Function.Bijective (F.map (X := X⟦n⟧) (Y := Y⟦n⟧)) := by
  constructor
  · intro f g hfg
    obtain ⟨f, rfl⟩ := (shiftFunctor C n).map_surjective f
    obtain ⟨g, rfl⟩ := (shiftFunctor C n).map_surjective g
    have he := congrArg (fun k => k ≫ (F.commShiftIso n).hom.app Y) hfg
    rw [F.commShiftIso_hom_naturality, F.commShiftIso_hom_naturality] at he
    have hh := (cancel_epi ((F.commShiftIso n).hom.app X)).1 he
    exact congrArg (fun k => (shiftFunctor C n).map k)
      (h.1 ((shiftFunctor T n).map_injective hh))
  · intro g
    let t := (shiftFunctor T n).preimage
      ((F.commShiftIso n).inv.app X ≫ g ≫ (F.commShiftIso n).hom.app Y)
    obtain ⟨f, hf⟩ := h.2 t
    refine ⟨f⟦n⟧', ?_⟩
    apply (cancel_mono ((F.commShiftIso n).hom.app Y)).1
    rw [F.commShiftIso_hom_naturality, hf]
    dsimp only [t]
    rw [Functor.map_preimage]
    simp only [← Category.assoc, Iso.hom_inv_id_app]
    exact congrArg (fun k => k ≫ (F.commShiftIso n).hom.app Y) (Category.id_comp g)

/-- 固定した終域に対し、任意の始域からの関手の射写像が全単射。 -/
def homComparisonTarget : ObjectProperty C :=
  fun Y => ∀ X, Function.Bijective (F.map (X := X) (Y := Y))

instance homComparisonTargetClosedUnderIso :
    (homComparisonTarget F).IsClosedUnderIsomorphisms where
  of_iso e h X := homComparison_bijective_of_iso F (Iso.refl X) e (h X)

instance homComparisonTargetStableUnderShift :
    (homComparisonTarget F).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun Y h X => by
    let X' := (shiftFunctor C n).objPreimage X
    exact homComparison_bijective_of_iso F ((shiftFunctor C n).objObjPreimageIso X)
      (Iso.refl (Y⟦n⟧)) (homComparison_bijective_shift_both F (h X') n)⟩

end SerrePositivity.DifferentialGraded
end

end ShiftedHomComparison

/-! ## HorizontalComparison（旧 SerrePositivity/DifferentialGraded/Verdier/HorizontalComparison.lean） -/

/-! # 比較正方形の横貼合せと同型による経路の輸送 -/

@[expose] public section HorizontalComparison

namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor

section Horizontal
variable {C₀ C₁ C₂ V₀ V₁ V₂ : Type*}
  [Category* C₀] [Category* C₁] [Category* C₂]
  [Category* V₀] [Category* V₁] [Category* V₂]
  (L₀ : C₀ ⥤ V₀) (L₁ : C₁ ⥤ V₁) (L₂ : C₂ ⥤ V₂)
  {F F' : C₀ ⥤ C₁} {G G' : C₁ ⥤ C₂}
  {Fbar Fbar' : V₀ ⥤ V₁} {Gbar Gbar' : V₁ ⥤ V₂}
  (a : L₀ ⋙ Fbar ≅ F ⋙ L₁) (a' : L₀ ⋙ Fbar' ≅ F' ⋙ L₁)
  (b : L₁ ⋙ Gbar ≅ G ⋙ L₂) (b' : L₁ ⋙ Gbar' ≅ G' ⋙ L₂)
  (f : F ⟶ F') (g : G ⟶ G') (fbar : Fbar ⟶ Fbar') (gbar : Gbar ⟶ Gbar')

/-- 二つの比較正方形を横に貼り合わせた同型。 -/
def horizontalComparison : L₀ ⋙ (Fbar ⋙ Gbar) ≅ (F ⋙ G) ⋙ L₂ :=
  (associator _ _ _).symm ≪≫ isoWhiskerRight a Gbar ≪≫ associator _ _ _ ≪≫
    isoWhiskerLeft F b ≪≫ (associator _ _ _).symm

/-- 各比較が自然なら、その実際の横貼合せも水平合成に関して自然。 -/
lemma horizontalComparison_naturality
    (ha : whiskerLeft L₀ fbar ≫ a'.hom = a.hom ≫ whiskerRight f L₁)
    (hb : whiskerLeft L₁ gbar ≫ b'.hom = b.hom ≫ whiskerRight g L₂) :
    whiskerLeft L₀ (NatTrans.hcomp fbar gbar) ≫
        (horizontalComparison L₀ L₁ L₂ a' b').hom =
      (horizontalComparison L₀ L₁ L₂ a b).hom ≫ whiskerRight (NatTrans.hcomp f g) L₂ := by
  apply NatTrans.ext
  funext X
  have hax := NatTrans.congr_app ha X
  have hbx := NatTrans.congr_app hb (F.obj X)
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hax hbx
  have hn := b'.hom.naturality (f.app X)
  simp only [Functor.comp_map] at hn
  have hg := gbar.naturality (a.hom.app X)
  simp only [horizontalComparison, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    associator_inv_app, associator_hom_app, NatTrans.hcomp_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  rw [← Gbar'.map_comp_assoc, hax, Gbar'.map_comp, Category.assoc,
    hn, ← reassoc_of% hg, reassoc_of% hbx, ← L₂.map_comp]
end Horizontal

section Transport
variable {C : Type*} [Category* C]
  {X X' Y Y' A A' B B' : C}
  (a : X ≅ A) (a' : X' ≅ A') (b : Y ≅ B) (b' : Y' ≅ B')
  (e : A ≅ B) (e' : A' ≅ B') (fbar : X ⟶ X') (gbar : Y ⟶ Y')
  (f : A ⟶ A') (g : B ⟶ B')

/-- 元の比較と両側の表示変更が自然なら、輸送した比較も同じ射に自然。 -/
lemma transportedComparison_naturality
    (ha : fbar ≫ a'.hom = a.hom ≫ f)
    (hb : gbar ≫ b'.hom = b.hom ≫ g) (he : f ≫ e'.hom = e.hom ≫ g) :
    fbar ≫ a'.hom ≫ e'.hom ≫ b'.inv = a.hom ≫ e.hom ≫ b.inv ≫ gbar := by
  apply (cancel_mono b'.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, ha]
  simp only [Category.assoc]
  rw [he, hb]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.comp_id]
end Transport
end SerrePositivity.DifferentialGraded

end HorizontalComparison

/-! ## TriangulatedHomComparison（旧 SerrePositivity/DifferentialGraded/Verdier/TriangulatedHomComparison.lean） -/

/-! # 三角関手の Hom 全単射性を持つ終域の三角閉性 -/

@[expose] public section TriangulatedHomComparison
universe u₁ u₂ v₁ v₂

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated Preadditive
open scoped ZeroObject
variable {C : Type u₁} [Category.{v₁} C] {T : Type u₂} [Category.{v₂} T]
  [HasZeroObject C] [HasZeroObject T] [Preadditive C] [Preadditive T]
  [HasShift C ℤ] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated C] [Pretriangulated T]
  (F : C ⥤ T) [F.CommShift ℤ] [F.IsTriangulated] [F.Additive]

/-- 三角形の両端への Hom が保存されれば、中間対象への Hom も保存される。 -/
lemma homComparisonTarget_triangle_obj₂ (t : Triangle C) (ht : t ∈ distTriang C)
    (h₁ : homComparisonTarget F t.obj₁) (h₃ : homComparisonTarget F t.obj₃) :
    homComparisonTarget F t.obj₂ := by
  intro X
  have h₁s := (homComparisonTarget F).le_shift (1 : ℤ) _ h₁
  have h₃s := (homComparisonTarget F).le_shift (-1 : ℤ) _ h₃
  have hker : ∀ f : X ⟶ t.obj₂, F.map f = 0 → f = 0 := by
    intro f hf
    have hz : f ≫ t.mor₂ = 0 := (h₃ X).1 (by
      rw [Functor.map_comp, hf, zero_comp, Functor.map_zero])
    obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₂ t ht f hz
    have haz : F.map a ≫ (F.mapTriangle.obj t.invRotate).mor₂ = 0 := by
      change F.map a ≫ F.map t.mor₁ = 0
      rw [← Functor.map_comp, ← ha, hf]
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ (F.mapTriangle.obj t.invRotate)
      (F.map_distinguished _ (inv_rot_of_distTriang _ ht)) (F.map a) haz
    obtain ⟨c, hc⟩ := (h₃s X).2 b
    have hac : a = c ≫ t.invRotate.mor₁ := (h₁ X).1 (by
      rw [Functor.map_comp, hc]
      exact hb)
    rw [ha, hac, Category.assoc]
    have hi : t.invRotate.mor₁ ≫ t.mor₁ = 0 :=
      comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang _ ht)
    rw [hi, comp_zero]
  constructor
  · intro f g hfg
    have hz : F.map (f - g) = 0 := by rw [Functor.map_sub, hfg, sub_self]
    exact sub_eq_zero.mp (hker (f - g) hz)
  · intro f
    obtain ⟨c, hc⟩ := (h₃ X).2 (f ≫ F.map t.mor₂)
    have hz : c ≫ t.mor₃ = 0 := (h₁s X).1 (by
      rw [Functor.map_comp, hc, Category.assoc, ← Functor.map_comp,
        comp_distTriang_mor_zero₂₃ _ ht, Functor.map_zero, comp_zero]
      exact (F.map_zero _ _).symm)
    obtain ⟨d, hd⟩ := Triangle.coyoneda_exact₃ t ht c hz
    have hdiff : (f - F.map d) ≫ (F.mapTriangle.obj t).mor₂ = 0 := by
      change (f - F.map d) ≫ F.map t.mor₂ = 0
      rw [sub_comp, ← Functor.map_comp, ← hd, hc, sub_self]
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ (F.mapTriangle.obj t)
      (F.map_distinguished _ ht) (f - F.map d) hdiff
    obtain ⟨a, ha⟩ := (h₁ X).2 b
    refine ⟨d + a ≫ t.mor₁, ?_⟩
    rw [Functor.map_add, Functor.map_comp, ha]
    have hb' : f - F.map d = b ≫ F.map t.mor₁ := hb
    rw [← hb']
    abel

instance homComparisonTargetTriangulatedClosed₂ :
    (homComparisonTarget F).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (homComparisonTarget_triangle_obj₂ F)

instance homComparisonTargetContainsZero : (homComparisonTarget F).ContainsZero :=
  ⟨⟨0, isZero_zero C, fun X => by
    constructor
    · intro f g _
      exact (isZero_zero C).eq_of_tgt f g
    · intro f
      exact ⟨0, (F.map_isZero (isZero_zero C)).eq_of_tgt _ _⟩⟩⟩

instance homComparisonTargetIsTriangulated : (homComparisonTarget F).IsTriangulated where

end SerrePositivity.DifferentialGraded
end

end TriangulatedHomComparison

/-! ## AdjunctionComparisonShift（旧 SerrePositivity/DifferentialGraded/Verdier/AdjunctionComparisonShift.lean） -/

/-! # 随伴の一意性による実際の比較同型の shift 整合性 -/

@[expose] public section AdjunctionComparisonShift

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor
variable {M : Type*} [AddMonoid M] {C D : Type*} [Category* C] [Category* D]
  [HasShift C M] [HasShift D M]

/-- 同じ右随伴への二つの整合的随伴から得る既存の一意性同型は shift と可換する。 -/
lemma leftAdjointUniqCommShift {F F' : C ⥤ D} {R : D ⥤ C}
    [F.CommShift M] [F'.CommShift M] [R.CommShift M]
    (a : F ⊣ R) (b : F' ⊣ R) [a.CommShift M] [b.CommShift M] :
    NatTrans.CommShift (Adjunction.leftAdjointUniq a b).hom M := by
  let τ : F ⟶ F' :=
    F.leftUnitor.inv ≫ whiskerRight b.unit F ≫ (associator F' R F).hom ≫
      whiskerLeft F' a.counit ≫ F'.rightUnitor.hom
  have hτ : NatTrans.CommShift τ M := by
    dsimp [τ]
    infer_instance
  have he : (Adjunction.leftAdjointUniq a b).hom = τ := by
    apply NatTrans.ext
    funext X
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app a b X
    have h' := (a.homEquiv X (F'.obj X)).symm_apply_apply
      ((Adjunction.leftAdjointUniq a b).hom.app X)
    rw [h] at h'
    simp only [τ, NatTrans.comp_app, leftUnitor_inv_app, whiskerRight_app,
      associator_hom_app, whiskerLeft_app, rightUnitor_hom_app,
      Category.id_comp]
    rw [Adjunction.homEquiv_counit] at h'
    exact h'.symm.trans (congrArg (fun f => F.map (b.unit.app X) ≫ f)
      (Category.comp_id (a.counit.app (F'.obj X))).symm)
  rw [he]
  exact hτ

/-- 右関手の整合的自然同型による随伴の輸送は、既存の両 shift を保つ。 -/
lemma adjunctionOfNatIsoRightCommShift {F : C ⥤ D} {R R' : D ⥤ C}
    [F.CommShift M] [R.CommShift M] [R'.CommShift M]
    (a : F ⊣ R) [a.CommShift M] (e : R ≅ R') [NatTrans.CommShift e.hom M] :
    (a.ofNatIsoRight e).CommShift M := by
  apply Adjunction.CommShift.mk'
  change NatTrans.CommShift (a.unit ≫ whiskerLeft F e.hom) M
  infer_instance
end SerrePositivity.DifferentialGraded
end

end AdjunctionComparisonShift

/-! ## DerivedCoproductComparison（旧 SerrePositivity/DifferentialGraded/Verdier/DerivedCoproductComparison.lean） -/

/-! # 加群の擬同型の余積と導来局所化の余積保存

各評価の exact な余極限と、通常の加群の射影置換を用いる。
-/

@[expose] public section DerivedCoproductComparison
universe u v w w'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma module_colimMap_quasiIso {J : Type w} [Category.{w'} J] [Small.{u} J]
    [HasColimitsOfShape J (ModuleCat.{u} A)] [HasExactColimitsOfShape J (ModuleCat.{u} A)]
    {F G : J ⥤ ModuleCategory A D} (α : F ⟶ G)
    (hα : ∀ j, moduleQuasiIso A D (α.app j)) : moduleQuasiIso A D (colimMap α) := by
  have : HasColimitsOfShape J (Complex A) :=
    ⟨fun H => HasColimit.mk ⟨_, isColimitCoconeOfHasColimitEval H⟩⟩
  intro x
  let E := moduleEvaluation A D x
  have : QuasiIso (colimMap (Functor.whiskerRight α E)) :=
    DGQuotient.complex_colimMap_quasiIso A _ (fun j => hα j x)
  have h := (preservesColimitNatIso E).hom.naturality α
  change E.map (colimMap α) ≫ (preservesColimitIso E G).hom =
    (preservesColimitIso E F).hom ≫ colimMap (Functor.whiskerRight α E) at h
  have : QuasiIso (E.map (colimMap α) ≫ (preservesColimitIso E G).hom) := by
    rw [h]
    infer_instance
  exact quasiIso_of_comp_right (E.map (colimMap α)) (preservesColimitIso E G).hom

variable {I : Type w} [Small.{u} I]

private lemma sigmaMap_eq_colimMap {C : Type*} [Category* C] {J : Type*}
    (M N : J → C) [HasCoproduct M] [HasCoproduct N] (q : ∀ i, M i ⟶ N i) :
    Limits.Sigma.map q = colimMap (Discrete.natTrans (F := Discrete.functor M)
      (G := Discrete.functor N) (fun i => q i.as)) := rfl

/-- 任意の u-small 族の objectwise 擬同型の直和は擬同型。 -/
lemma module_coproductMap_quasiIso {M N : I → ModuleCategory A D}
    (q : ∀ i, M i ⟶ N i) (hq : ∀ i, moduleQuasiIso A D (q i)) :
    moduleQuasiIso A D (Limits.Sigma.map q) := by
  have : HasExactColimitsOfShape (Discrete I) (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (Discrete.equivalence (equivShrink.{u} I).symm)
  rw [sigmaMap_eq_colimMap M N q]
  exact module_colimMap_quasiIso A D (F := Discrete.functor M) (G := Discrete.functor N)
    (Discrete.natTrans (fun i => q i.as)) (fun i => hq i.as)

/-- 射影性を仮定しない任意の加群族でも、局所化した余積包含は導来圏の余積となる。 -/
def moduleDerivedCofanIsColimit (M : I → ModuleCategory A D) :
    IsColimit (moduleProjectiveDerivedCofan A D M) := by
  let R := fun i => moduleCanonicalProjectiveResolution A D (M i)
  let P := fun i => (R i).obj
  let q := fun i => (R i).π
  let e := moduleDerivedIso A D (Limits.Sigma.map q)
    (module_coproductMap_quasiIso A D q (fun i => (R i).quasiIso))
  let α : Discrete.functor (fun i => (moduleToDerived A D).obj (P i)) ≅
      Discrete.functor (fun i => (moduleToDerived A D).obj (M i)) :=
    Discrete.natIso (fun i => moduleDerivedIso A D (q i.as) (R i.as).quasiIso)
  refine (IsColimit.precomposeHomEquiv α (moduleProjectiveDerivedCofan A D M))
    (IsColimit.ofIsoColimit
      (moduleProjectiveDerivedCofanIsColimit A D P (fun i => (R i).projective)) ?_)
  refine Cocone.ext e ?_
  rintro ⟨i⟩
  change (moduleToDerived A D).map (Sigma.ι P i) ≫
      (moduleToDerived A D).map (Limits.Sigma.map q) =
    (moduleToDerived A D).map (q i) ≫ (moduleToDerived A D).map (Sigma.ι M i)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, Sigma.ι_map]

/-- 導来圏の選ばれた余積と、underived 余積の局所化との比較。 -/
def moduleDerivedCoproductIso (M : I → ModuleCategory A D) :
    (∐ fun i => (moduleToDerived A D).obj (M i)) ≅ (moduleToDerived A D).obj (∐ M) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (moduleDerivedCofanIsColimit A D M)

@[reassoc] lemma moduleDerivedCoproductIso_ι (M : I → ModuleCategory A D) (i : I) :
    Sigma.ι (fun i => (moduleToDerived A D).obj (M i)) i ≫
      (moduleDerivedCoproductIso A D M).hom = (moduleToDerived A D).map (Sigma.ι M i) := by
  let hc := colimit.isColimit (Discrete.functor (fun i => (moduleToDerived A D).obj (M i)))
  exact hc.comp_coconePointUniqueUpToIso_hom _ ⟨i⟩

instance moduleToDerived_preservesCoproduct (M : I → ModuleCategory A D) :
    PreservesColimit (Discrete.functor M) (moduleToDerived A D) :=
  preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct M)
    ((isColimitMapCoconeCofanMkEquiv (moduleToDerived A D) M (Sigma.ι M)).symm
      (moduleDerivedCofanIsColimit A D M))

instance moduleToDerived_preservesCoproducts :
    PreservesColimitsOfShape (Discrete I) (moduleToDerived A D) :=
  preservesColimitsOfShape_of_discrete _

end SerrePositivity.DifferentialGraded
end

end DerivedCoproductComparison

/-! ## Tria（旧 SerrePositivity/DifferentialGraded/Verdier/Tria.lean） -/

/-! # 既存の有限 cell 本質像としての tria(D)

tria は retract を加える前の三角部分圏であり、Perf とは区別する。
部分集合 S は、後続の明示的 dg 商で殺す full 部分圏と同じ対象添字である。
-/

@[expose] public section Tria
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 既存の有限 cell 本質像の充満三角部分圏 tria(D)。 -/
abbrev TriaCategory := DerivedFiniteCellCategoryOver A D Set.univ

abbrev triaInclusion : TriaCategory A D ⥤ DerivedModuleCategory A D :=
  derivedFiniteCellInclusion A D Set.univ

/-- tria(D) 内で考える、S の代表加群からの三角閉包。 -/
def triaImage (S : Set D) : ObjectProperty (TriaCategory A D) :=
  (derivedFiniteCellOver A D S).inverseImage (triaInclusion A D)

instance triaImageClosedUnderIso (S : Set D) :
    (triaImage A D S).IsClosedUnderIsomorphisms := by
  dsimp [triaImage]
  infer_instance

instance triaImageIsTriangulated (S : Set D) : (triaImage A D S).IsTriangulated := by
  dsimp [triaImage]
  infer_instance

/-- tria(D) の指定代表対象。 -/
def triaRepresentable (x : D) : TriaCategory A D :=
  ⟨(moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)),
    (moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToDerived A D)
      (moduleFiniteCell_representable A D x)⟩

lemma triaImage_representable (S : Set D) (x : D) (hx : x ∈ S) :
    triaImage A D S (triaRepresentable A D x) :=
  (moduleFiniteCellOver A D S).prop_map_obj (moduleToDerived A D)
    (moduleFiniteCellOver_representable A D x hx)

/-- tria(D) 内の三角部分圏に対する生成性。 -/
lemma triaImage_le_iff_generators (S : Set D)
    (P : ObjectProperty (TriaCategory A D)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] :
    triaImage A D S ≤ P ↔ ∀ x ∈ S, P (triaRepresentable A D x) := by
  constructor
  · intro h x hx
    exact h _ (triaImage_representable A D S x hx)
  · intro h X hX
    have hle : derivedFiniteCellOver A D S ≤ P.map (triaInclusion A D) :=
      (derivedFiniteCellOver_le_iff_generators A D
        (P.map (triaInclusion A D)) S).2
        (fun x hx => P.prop_map_obj (triaInclusion A D) (h x hx))
    obtain ⟨Y, hY, ⟨e⟩⟩ := hle _ hX
    exact P.prop_of_iso ((triaInclusion A D).preimageIso e) hY

/-- 後続の Karoubi/Verdier 比較で使う厚い零対象クラス。 -/
abbrev triaNull (S : Set D) : ObjectProperty (TriaCategory A D) :=
  (triaImage A D S).triangEnvelope

/-- tria(D)/tria(S) の既存の指定 Verdier 局所化。 -/
abbrev TriaQuotient (S : Set D) := (triaImage A D S).trW.Localization

abbrev triaQuotient (S : Set D) : TriaCategory A D ⥤ TriaQuotient A D S :=
  (triaImage A D S).trW.Q

/-- U17b の比較先。局所化・Karoubi の新しい一般構成を導入しない。 -/
abbrev CompletedTriaQuotient (S : Set D) :=
  CategoryTheory.Idempotents.Karoubi (TriaQuotient A D S)

/-- U17c の既存の順序交換同値に渡す、同じ三角部分圏。 -/
abbrev triaKaroubiOrderEquivalence (S : Set D) :
    CategoryTheory.Idempotents.Karoubi (KaroubiFirstQuotient (triaImage A D S)) ≌
      CompletedTriaQuotient A D S :=
  karoubiVerdierOrderEquivalence (triaImage A D S)

/-- 完備化を先に行う側の標準関手。 -/
abbrev triaKaroubiFirst (S : Set D) := karoubiFirstFromOriginal (triaImage A D S)

/-- `paperSequenceComparison` と同じ向きの標準関手の比較。 -/
def triaKaroubiComparison (S : Set D) :
    triaKaroubiFirst A D S ⋙ (triaKaroubiOrderEquivalence A D S).functor ≅
      triaQuotient A D S ⋙ CategoryTheory.Idempotents.toKaroubi _ :=
  isoWhiskerLeft (CategoryTheory.Idempotents.toKaroubi _ ⋙
      (karoubiNullEnvelope (triaImage A D S)).trW.Q)
    (completedKaroubiFirstToLastFactors _) ≪≫
  isoWhiskerLeft (CategoryTheory.Idempotents.toKaroubi _) (karoubiFirstToLastFactors _) ≪≫
  (CategoryTheory.Idempotents.functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app
    (triaQuotient A D S)

end SerrePositivity.DifferentialGraded
end

end Tria

/-! ## NullObjects（旧 SerrePositivity/DifferentialGraded/Verdier/NullObjects.lean） -/

/-! # Verdier 商で殺される対象と retract 閉包

既存の分数計算と三角形の Hom 完全性を使い、零対象の逆像を判定する。
-/

@[expose] public section NullObjects
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
open scoped ZeroObject

section
variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (P : ObjectProperty C) [P.IsTriangulated]

/-- 三角部分圏による Verdier 商は、ちょうどその retract 閉包を殺す。 -/
lemma verdierQuotient_isZero_iff_retractClosure (X : C) :
    IsZero (P.trW.Q.obj X) ↔ P.retractClosure X := by
  constructor
  · intro hX
    have hmap : P.trW.Q.map (𝟙 X) = P.trW.Q.map (0 : X ⟶ X) := by
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
      exact (IsZero.iff_id_eq_zero _).1 hX
    obtain ⟨Y, s, hs, hfac⟩ :=
      (MorphismProperty.map_eq_iff_precomp P.trW.Q P.trW (𝟙 X) 0).1 hmap
    have hs0 : s = 0 := by simpa only [Category.comp_id, Limits.comp_zero] using hfac
    obtain ⟨Z, g, h, hT, hZ⟩ := hs
    obtain ⟨r, hr⟩ := Triangle.yoneda_exact₂ _ hT (𝟙 X)
      (by change s ≫ 𝟙 X = 0; rw [Category.comp_id]; exact hs0)
    exact ⟨Z, hZ, ⟨{ i := g, r := r, retract := hr.symm }⟩⟩
  · rintro ⟨Y, hY, ⟨r⟩⟩
    exact (triangulatedKernel P.trW.Q).prop_of_retract r (verdierQuotient_isZero P Y hY)

/-- 商の三角関手の核を、元の対象クラスで記述する。 -/
lemma verdierQuotient_kernel_eq_retractClosure :
    triangulatedKernel P.trW.Q = P.retractClosure := by
  funext X
  exact propext (verdierQuotient_isZero_iff_retractClosure P X)

/-- 三角部分圏の thick 閉包は retract 閉包だけで得られる。 -/
lemma triangEnvelope_eq_retractClosure : P.triangEnvelope = P.retractClosure := by
  have : P.retractClosure.IsTriangulated := by
    rw [← verdierQuotient_kernel_eq_retractClosure P]
    infer_instance
  apply le_antisymm
  · exact P.triangEnvelope_le_iff.2 P.le_retractClosure
  · exact (ObjectProperty.retractClosure_le_iff P P.triangEnvelope).2 P.le_triangEnvelope

end

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- tria 内の retract 閉包と、同じ導来対象に対する Perf_S は一致する。 -/
lemma triaImage_retractClosure_iff_perfect (S : Set D) (X : TriaCategory A D) :
    (triaImage A D S).retractClosure X ↔ modulePerfectOver A D S X.obj := by
  constructor
  · rintro ⟨Y, hY, ⟨r⟩⟩
    exact ObjectProperty.prop_retractClosure hY (r.map (triaInclusion A D))
  · rintro ⟨Y, hY, ⟨r⟩⟩
    have hYu : derivedFiniteCellOver A D Set.univ Y :=
      ObjectProperty.map_monotone
        (fun _ hM => moduleFiniteCellOver_mono A D (Set.subset_univ S) hM)
        (moduleToDerived A D) Y hY
    let Y' : TriaCategory A D := ⟨Y, hYu⟩
    let r' : Retract X Y' :=
      { i := ObjectProperty.homMk r.i
        r := ObjectProperty.homMk r.r
        retract := by ext; exact r.retract }
    exact ⟨Y', hY, ⟨r'⟩⟩

/-- U17a の零対象判定。tria(S) の retract 閉包との一致を明示する。 -/
lemma triaQuotient_isZero_iff (S : Set D) (X : TriaCategory A D) :
    IsZero ((triaQuotient A D S).obj X) ↔ (triaImage A D S).retractClosure X :=
  verdierQuotient_isZero_iff_retractClosure (triaImage A D S) X

lemma triaQuotient_isZero_iff_triaNull (S : Set D) (X : TriaCategory A D) :
    IsZero ((triaQuotient A D S).obj X) ↔ triaNull A D S X := by
  rw [triaNull, triangEnvelope_eq_retractClosure]
  exact triaQuotient_isZero_iff A D S X

lemma triaQuotient_isZero_iff_perfect (S : Set D) (X : TriaCategory A D) :
    IsZero ((triaQuotient A D S).obj X) ↔ modulePerfectOver A D S X.obj :=
  (triaQuotient_isZero_iff A D S X).trans
    (triaImage_retractClosure_iff_perfect A D S X)

end SerrePositivity.DifferentialGraded
end

end NullObjects

/-! ## FiniteCellHomotopy（旧 SerrePositivity/DifferentialGraded/Verdier/FiniteCellHomotopy.lean） -/

/-! # 有限 cell の K(D) 内の像と tria(D) の三角同値

有限 cell の射影性により、主導来局所化はこの部分圏上で完全忠実となる。
dg 圏の解像度は用いない。
-/

@[expose] public section FiniteCellHomotopy
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- retract を加えない有限 cell の K(D) 内の本質像。 -/
def homotopyFiniteCellOver (S : Set D) : ObjectProperty (ModuleHomotopyCategory A D) :=
  (moduleFiniteCellOver A D S).map (moduleToHomotopy A D)

instance homotopyFiniteCellOverClosedUnderIso (S : Set D) :
    (homotopyFiniteCellOver A D S).IsClosedUnderIsomorphisms := by
  dsimp [homotopyFiniteCellOver]
  infer_instance

instance homotopyFiniteCellOverShift (S : Set D) :
    (homotopyFiniteCellOver A D S).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨by
    rintro X ⟨M, hM, ⟨e⟩⟩
    exact ⟨M⟦n⟧, moduleFiniteCellOver_shift A D hM n,
      ⟨((moduleToHomotopy A D).commShiftIso n).app M ≪≫
        (shiftFunctor _ n).mapIso e⟩⟩⟩

lemma homotopyFiniteCellOver_triangle_obj₃ (S : Set D)
    (T : Triangle (ModuleHomotopyCategory A D))
    (hT : T ∈ distTriang (ModuleHomotopyCategory A D))
    (h₁ : homotopyFiniteCellOver A D S T.obj₁)
    (h₂ : homotopyFiniteCellOver A D S T.obj₂) : homotopyFiniteCellOver A D S T.obj₃ := by
  obtain ⟨M, hM, ⟨eM⟩⟩ := h₁
  obtain ⟨N, hN, ⟨eN⟩⟩ := h₂
  obtain ⟨f, hf⟩ := (moduleToHomotopy A D).map_surjective (eM.hom ≫ T.mor₁ ≫ eN.inv)
  have he : Arrow.mk (moduleHomotopyConeTriangle A D f).mor₁ ≅ Arrow.mk T.mor₁ :=
    Arrow.isoMk eM eN (by
      change eM.hom ≫ T.mor₁ = (moduleToHomotopy A D).map f ≫ eN.hom
      rw [hf]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
  obtain ⟨e, _⟩ := exists_iso_of_arrow_iso (moduleHomotopyConeTriangle A D f) T
    (moduleHomotopyConeTriangle_distinguished A D f) hT he
  exact ⟨moduleCone A D f, moduleFiniteCellOver_cone A D hM hN f, ⟨Triangle.π₃.mapIso e⟩⟩

instance homotopyFiniteCellOverClosed₃ (S : Set D) :
    (homotopyFiniteCellOver A D S).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk' (homotopyFiniteCellOver_triangle_obj₃ A D S)

instance homotopyFiniteCellOverClosed₂ (S : Set D) :
    (homotopyFiniteCellOver A D S).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

instance homotopyFiniteCellOverContainsZero (S : Set D) :
    (homotopyFiniteCellOver A D S).ContainsZero :=
  ⟨⟨(moduleToHomotopy A D).obj (moduleZero A D),
    (moduleToHomotopy A D).map_isZero (moduleZero_isZero A D),
    (moduleFiniteCellOver A D S).prop_map_obj (moduleToHomotopy A D)
      (moduleFiniteCellOver_zero A D S)⟩⟩

instance homotopyFiniteCellOverIsTriangulated (S : Set D) :
    (homotopyFiniteCellOver A D S).IsTriangulated where

abbrev HomotopyFiniteCellCategoryOver (S : Set D) := (homotopyFiniteCellOver A D S).FullSubcategory

/-- 有限 cell の像を始域とする局所化 Hom 写像は全単射。 -/
lemma homotopyFiniteCell_localization_map_bijective {S : Set D}
    {X : ModuleHomotopyCategory A D} (hX : homotopyFiniteCellOver A D S X)
    (Y : ModuleHomotopyCategory A D) :
    Function.Bijective ((moduleHomotopyToDerivedClosed A D).map (X := X) (Y := Y)) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hX
  let L := moduleHomotopyToDerivedClosed A D
  have hb := moduleProjectiveLocalization_map_bijective A D
    (moduleFiniteCellOver_homotopicallyProjective A D hM) Y
  constructor
  · intro f g h
    have hh : e.hom ≫ f = e.hom ≫ g := hb.1 (by
      simp only [CategoryTheory.Functor.map_comp, h])
    exact (cancel_epi e.hom).mp hh
  · intro f
    obtain ⟨g, hg⟩ := hb.2 (L.map e.hom ≫ f)
    refine ⟨e.inv ≫ g, ?_⟩
    rw [CategoryTheory.Functor.map_comp, hg]
    change L.map e.inv ≫ L.map e.hom ≫ f = f
    simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- K(D) から主導来圏への既存関手の有限 cell 部分圏上の制限。 -/
def homotopyFiniteCellToDerived (S : Set D) :
    HomotopyFiniteCellCategoryOver A D S ⥤ DerivedModuleCategory A D :=
  (homotopyFiniteCellOver A D S).ι ⋙ moduleHomotopyToDerivedClosed A D

instance homotopyFiniteCellToDerivedFull (S : Set D) :
    (homotopyFiniteCellToDerived A D S).Full where
  map_surjective {X Y} f := by
    obtain ⟨g, hg⟩ := (homotopyFiniteCell_localization_map_bijective A D X.property Y.obj).2 f
    refine ⟨(homotopyFiniteCellOver A D S).ι.preimage g, ?_⟩
    change (moduleHomotopyToDerivedClosed A D).map
      ((homotopyFiniteCellOver A D S).ι.map ((homotopyFiniteCellOver A D S).ι.preimage g)) = f
    rw [Functor.map_preimage]
    exact hg

instance homotopyFiniteCellToDerivedFaithful (S : Set D) :
    (homotopyFiniteCellToDerived A D S).Faithful where
  map_injective {X Y} f g h := by
    apply (homotopyFiniteCellOver A D S).ι.map_injective
    exact (homotopyFiniteCell_localization_map_bijective A D X.property Y.obj).1 h

lemma homotopyFiniteCellToDerived_mem (S : Set D) (X : HomotopyFiniteCellCategoryOver A D S) :
    derivedFiniteCellOver A D S ((homotopyFiniteCellToDerived A D S).obj X) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := X.property
  exact ⟨M, hM, ⟨((moduleToHomotopyDerivedIso A D).app M).symm ≪≫
    (moduleHomotopyToDerivedClosed A D).mapIso e⟩⟩

/-- 有限 cell 同士では主導来局所化は三角同値。 -/
def homotopyFiniteCellToTria (S : Set D) :
    HomotopyFiniteCellCategoryOver A D S ⥤ DerivedFiniteCellCategoryOver A D S :=
  (derivedFiniteCellOver A D S).lift (homotopyFiniteCellToDerived A D S)
    (homotopyFiniteCellToDerived_mem A D S)

instance homotopyFiniteCellToTriaFull (S : Set D) :
    (homotopyFiniteCellToTria A D S).Full := by
  dsimp [homotopyFiniteCellToTria]
  infer_instance

instance homotopyFiniteCellToTriaFaithful (S : Set D) :
    (homotopyFiniteCellToTria A D S).Faithful := by
  dsimp [homotopyFiniteCellToTria]
  infer_instance

instance homotopyFiniteCellToTriaEssSurj (S : Set D) :
    (homotopyFiniteCellToTria A D S).EssSurj where
  mem_essImage X := by
    obtain ⟨M, hM, ⟨e⟩⟩ := X.property
    exact ⟨⟨(moduleToHomotopy A D).obj M,
      (moduleFiniteCellOver A D S).prop_map_obj (moduleToHomotopy A D) hM⟩,
      ⟨(derivedFiniteCellOver A D S).isoMk ((moduleToHomotopyDerivedIso A D).app M ≪≫ e)⟩⟩

instance homotopyFiniteCellToTriaIsEquivalence (S : Set D) :
    (homotopyFiniteCellToTria A D S).IsEquivalence where

instance homotopyFiniteCellToDerivedCommShift (S : Set D) :
    (homotopyFiniteCellToDerived A D S).CommShift ℤ := by
  dsimp [homotopyFiniteCellToDerived]
  infer_instance

instance homotopyFiniteCellToDerivedIsTriangulated (S : Set D) :
    (homotopyFiniteCellToDerived A D S).IsTriangulated := by
  dsimp [homotopyFiniteCellToDerived]
  infer_instance

instance homotopyFiniteCellToTriaCommShift (S : Set D) :
    (homotopyFiniteCellToTria A D S).CommShift ℤ := by
  dsimp [homotopyFiniteCellToTria]
  infer_instance

instance homotopyFiniteCellToTriaIsTriangulated (S : Set D) :
    (homotopyFiniteCellToTria A D S).IsTriangulated := by
  dsimp [homotopyFiniteCellToTria]
  infer_instance

def homotopyFiniteCellTriaEquivalence (S : Set D) :
    HomotopyFiniteCellCategoryOver A D S ≌ DerivedFiniteCellCategoryOver A D S :=
  (homotopyFiniteCellToTria A D S).asEquivalence

instance homotopyFiniteCellTriaEquivalenceFunctorCommShift (S : Set D) :
    (homotopyFiniteCellTriaEquivalence A D S).functor.CommShift ℤ :=
  homotopyFiniteCellToTriaCommShift A D S

instance homotopyFiniteCellTriaEquivalenceInverseCommShift (S : Set D) :
    (homotopyFiniteCellTriaEquivalence A D S).inverse.CommShift ℤ :=
  (homotopyFiniteCellTriaEquivalence A D S).commShiftInverse ℤ

instance homotopyFiniteCellTriaEquivalenceCommShift (S : Set D) :
    (homotopyFiniteCellTriaEquivalence A D S).CommShift ℤ :=
  (homotopyFiniteCellTriaEquivalence A D S).commShift_of_functor ℤ

instance homotopyFiniteCellTriaEquivalenceIsTriangulated (S : Set D) :
    (homotopyFiniteCellTriaEquivalence A D S).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (homotopyFiniteCellToTriaIsTriangulated A D S)

end SerrePositivity.DifferentialGraded
end

end FiniteCellHomotopy

/-! ## DerivedGeneratorInduction（旧 SerrePositivity/DifferentialGraded/Verdier/DerivedGeneratorInduction.lean） -/

/-! # 代表加群による導来圏の localizing 生成の帰納法

普通の dg 加群の標準解像度を使う。dg 圏の解像度は使わない。
-/

@[expose] public section DerivedGeneratorInduction
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
section
variable (P : ObjectProperty (DerivedModuleCategory A D)) [P.IsTriangulated]
  [P.IsClosedUnderIsomorphisms]
variable (hcoprod : ∀ (I : Type u) (F : I → DerivedModuleCategory A D),
  (∀ i, P (F i)) → P (∐ F))
include hcoprod

omit [P.IsTriangulated] in
lemma moduleGeneratorInduction_coproduct_small {I : Type w} [Small.{u} I]
    (F : I → DerivedModuleCategory A D) (hF : ∀ i, P (F i)) : P (∐ F) := by
  let e : Shrink.{u} I ≃ I := (equivShrink I).symm
  exact P.prop_of_iso (Sigma.reindex e F) (hcoprod _ (F ∘ e) (fun i => hF (e i)))

omit [P.IsTriangulated] in
lemma moduleGeneratorInduction_projectiveCoproduct {I : Type w} [Small.{u} I]
    (M : I → ModuleCategory A D) (hM : ∀ i, moduleHomotopicallyProjective A D (M i))
    (hF : ∀ i, P ((moduleToDerived A D).obj (M i))) :
    P ((moduleToDerived A D).obj (∐ M)) := by
  let hc := colimit.isColimit (Discrete.functor (fun i => (moduleToDerived A D).obj (M i)))
  exact P.prop_of_iso
    (hc.coconePointUniqueUpToIso (moduleProjectiveDerivedCofanIsColimit A D M hM))
    (moduleGeneratorInduction_coproduct_small A D P hcoprod _ hF)

variable (hgen : ∀ x : D, P ((moduleToDerived A D).obj
  (ForgetEnrichment.of (Complex A) (representable A x))))
include hgen

lemma moduleGeneratorInduction_sphereCoproduct {I : Type w} [Small.{u} I]
    (x : I → D) (n : I → ℤ) :
    P ((moduleToDerived A D).obj (∐ fun i => freeSphere A D (x i) (n i))) := by
  apply moduleGeneratorInduction_projectiveCoproduct A D P hcoprod _
    (fun i => freeSphere_homotopicallyProjective A D (x i) (n i))
  intro i
  apply (derivedFiniteCellOver_le_iff_generators A D P Set.univ).mpr
    (fun x _ => hgen x) _
  exact (moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToDerived A D)
    (moduleFiniteCellOver_freeSphere A D (x i) (Set.mem_univ _) (n i))

lemma moduleGeneratorInduction_resolutionStage (M : ModuleCategory A D) (n : ℕ) :
    P ((moduleToDerived A D).obj (moduleResolutionStage A D M n).left) := by
  induction n with
  | zero =>
    apply P.prop_of_isZero
    apply moduleToDerived_isZero_of_acyclic A D
    intro x i
    let : HasExactColimitsOfShape (Discrete (ModuleDiskCoverIndex A D M)) (ModuleCat.{u} A) :=
      HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
        (Discrete.equivalence (equivShrink.{u} (ModuleDiskCoverIndex A D M)).symm)
    exact (complex_colimit_acyclic A
      (Discrete.functor (moduleDiskCoverFamily A D M) ⋙ moduleEvaluation A D x)
      (fun j => freeDisk_acyclic A D j.as.1 j.as.2.1 x) i).of_iso
        (preservesColimitIso (moduleEvaluation A D x)
          (Discrete.functor (moduleDiskCoverFamily A D M))).symm
  | succ n ih =>
    exact P.ext_of_isTriangulatedClosed₃ _
      (moduleDerivedConeTriangle_distinguished A D
        (moduleKernelCellMap A D (moduleResolutionStage A D M n).hom))
      (moduleGeneratorInduction_sphereCoproduct A D P hcoprod hgen _ _) ih

lemma moduleGeneratorInduction_resolutionCandidate (M : ModuleCategory A D) :
    P ((moduleToDerived A D).obj (moduleResolutionCandidate A D M)) := by
  let F := moduleResolutionDiagram A D M
  let R := sequentialCoproductFamily.{u} F
  have hp (i : ULift.{u} ℕ) : moduleHomotopicallyProjective A D (R i) :=
    (moduleResolutionSemifreeFiltration A D M).stage_homotopicallyProjective A D (i.down + 1)
  have hR : P ((moduleToDerived A D).obj (∐ R)) :=
    moduleGeneratorInduction_projectiveCoproduct A D P hcoprod R hp
      (fun i => moduleGeneratorInduction_resolutionStage A D P hcoprod hgen M i.down)
  have hcone : P ((moduleToDerived A D).obj
      (moduleCone A D (sequentialCoproductMap.{u} F))) :=
    P.ext_of_isTriangulatedClosed₃ _
      (moduleDerivedConeTriangle_distinguished A D (sequentialCoproductMap.{u} F)) hR hR
  exact P.prop_of_iso
    (moduleDerivedIso A D (moduleSequentialConeDesc A D F (colimit.cocone F))
      (moduleSequentialConeDesc_quasiIso A D F (colimit.cocone F) (colimit.isColimit F))) hcone

/-- 同型・三角形・u-small 余積に閉じて全代表加群を含む性質は、全導来対象で成立。 -/
lemma moduleDerived_generatorInduction (X : DerivedModuleCategory A D) : P X := by
  obtain ⟨⟨M⟩⟩ := X
  exact P.prop_of_iso
    (moduleDerivedIso A D (moduleResolutionCandidateπ A D M)
      (moduleResolutionCandidateπ_quasiIso A D M))
    (moduleGeneratorInduction_resolutionCandidate A D P hcoprod hgen M)

end

/-- 余積と三角形を保つ導来関手の像の性質も、全代表加群上で検証すればよい。 -/
lemma moduleDerived_functor_generatorInduction
    (E : Type w) [DGCategory A E] [Small.{u} E]
    (F : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    [F.CommShift ℤ] [F.IsTriangulated]
    (P : ObjectProperty (DerivedModuleCategory A E)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms]
    (hcoprod : ∀ (I : Type u) (G : I → DerivedModuleCategory A E),
      (∀ i, P (G i)) → P (∐ G))
    (hFcoprod : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) F)
    (hgen : ∀ x : D, P (F.obj ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x)))))
    (X : DerivedModuleCategory A D) : P (F.obj X) := by
  refine moduleDerived_generatorInduction A D (P.inverseImage F) ?_ hgen X
  intro I G hG
  let := hFcoprod I
  exact P.prop_of_iso (PreservesCoproduct.iso F G).symm
    (hcoprod I (fun i => F.obj (G i)) hG)

end SerrePositivity.DifferentialGraded
end

end DerivedGeneratorInduction

/-! ## DerivedGraphComposition（旧 SerrePositivity/DifferentialGraded/Verdier/DerivedGraphComposition.lean） -/

/-! # 導来 graph 延長の合成比較

置換の合成を同一視せず、実際の導来制限と随伴の一意性を使う。
-/

@[expose] public section DerivedGraphComposition
universe u v w t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

private lemma postcompose_identity (P Q : Complex A) : homPostcompose P (𝟙 Q) = 𝟙 _ :=
  (homFunctor P).map_id Q

private lemma precompose_identity (P Q : Complex A) : homPrecompose (𝟙 P) Q = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact CochainComplex.HomComplex.Cochain.id_comp z

def graphRestrictionCompositionIso :
    moduleRestriction A E T G.op ⋙ moduleRestriction A D E F.op ≅
      moduleRestriction A D T (F.comp G).op :=
  NatIso.ofComponents (fun M => moduleIsoMk A D (fun _ => Iso.refl _) (by
    intro x y
    change (F.map y.unop x.unop ≫
      (G.map (F.obj y.unop) (F.obj x.unop) ≫
        (ForgetEnrichment.to (Complex A) M).map (Opposite.op (G.obj (F.obj x.unop)))
          (Opposite.op (G.obj (F.obj y.unop))))) ≫ _ =
      ((F.map y.unop x.unop ≫ G.map (F.obj y.unop) (F.obj x.unop)) ≫
        (ForgetEnrichment.to (Complex A) M).map (Opposite.op (G.obj (F.obj x.unop)))
          (Opposite.op (G.obj (F.obj y.unop)))) ≫ _
    dsimp only [Iso.refl_hom]
    rw [postcompose_identity, precompose_identity]
    simp only [Category.assoc]
    rfl))
    (by
      intro M N f
      apply moduleMorphism_ext
      intro x
      simp only [CategoryTheory.Functor.map_comp, moduleIsoMk_hom_eval,
        Iso.refl_hom, Functor.comp_map, moduleRestriction_map_eval]
      change (moduleEvaluation A T (G.obj (F.obj x))).map f ≫ 𝟙 _ =
        𝟙 _ ≫ (moduleEvaluation A T (G.obj (F.obj x))).map f
      simp only [Category.comp_id, Category.id_comp])

def derivedGraphRestrictionCompositionIso :
    dgDerivedRestriction A E T G ⋙ dgDerivedRestriction A D E F ≅
      dgDerivedRestriction A D T (F.comp G) :=
  (Localization.fullyFaithfulWhiskeringLeft (moduleToDerived A T) (moduleQuasiIso A T)
    (DerivedModuleCategory A D)).preimageIso
    ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (eqToIso (dgDerivedRestriction_fac A E T G)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (eqToIso (dgDerivedRestriction_fac A D E F)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (graphRestrictionCompositionIso A D E T F G) _ ≪≫
      (eqToIso (dgDerivedRestriction_fac A D T (F.comp G))).symm)

/-- 任意の dg 関手の導来 graph 延長は、関手の合成と自然同型で両立する。 -/
def derivedGraphExtensionCompositionIso :
    dgDerivedExtension A D E F ⋙ dgDerivedExtension A E T G ≅
      dgDerivedExtension A D T (F.comp G) :=
  Adjunction.leftAdjointUniq
    ((dgDerivedExtensionRestrictionAdjunction A D E F).comp
      (dgDerivedExtensionRestrictionAdjunction A E T G))
    ((dgDerivedExtensionRestrictionAdjunction A D T (F.comp G)).ofNatIsoRight
      (derivedGraphRestrictionCompositionIso A D E T F G).symm)
end SerrePositivity.DifferentialGraded
end

end DerivedGraphComposition

/-! ## GraphRestrictionShift（旧 SerrePositivity/DifferentialGraded/Verdier/GraphRestrictionShift.lean） -/

/-! # graph 制限の合成比較と既存 shift の整合性 -/

@[expose] public section GraphRestrictionShift
universe u v w t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

local instance restrictionCompositionShift :
    (dgModuleRestriction A D E F.op).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A E D (dgModuleRestriction A D E F.op)

/-- 制限の正規化 shift 比較は各評価次数で恒等射である。 -/
lemma graphRestrictionShift_hom_eval (s : ℤ) (M : ModuleCategory A E) (d : D) (i : ℤ) :
    ((moduleEvaluation A D d).map
      (((dgModuleRestriction A D E F.op).onClosed.commShiftIso s).hom.app M)).f i = 𝟙 _ := by
  change ((moduleEvaluation A D d).map
    ((normalizedDGModuleFunctorCommShiftIso A E D
      (dgModuleRestriction A D E F.op) s).hom.app M)).f i = _
  have he : (normalizedDGModuleFunctorCommShiftIso A E D
      (dgModuleRestriction A D E F.op) s).hom.app M =
      (normalizedDGModuleFunctorShiftIso A E D (dgModuleRestriction A D E F.op) s
        (ForgetEnrichment.to (Complex A) M)).hom := by
    simp only [normalizedDGModuleFunctorCommShiftIso, moduleShiftFunctor_eq]
    rfl
  rw [he, normalizedDGModuleFunctorShiftIso_hom_eval_f]
  change ((moduleHomπ A D _ _ d).f s
    ((moduleRestrictionHom A D E F.op _ _).f s
      (normalizedModuleShiftOut A E s (ForgetEnrichment.to (Complex A) M)))).v i (i + s) rfl = _
  have h := congrArg (fun k => (k.f s
    (normalizedModuleShiftOut A E s (ForgetEnrichment.to (Complex A) M))).v i (i + s) rfl)
    (moduleRestrictionHom_π A D E F.op _ _ d)
  exact h.trans (normalizedModuleShiftOut_v A E s _ (F.obj d) i)
variable (T : Type t) [DGCategory A T] [Small.{u} T] (G : DGFunctor A E T)

/-- 元の合成比較を、全 Hom の dg 制限の閉零関手として表示する。 -/
def graphRestrictionEnrichedCompositionIso :
    (dgModuleRestriction A E T G.op).onClosed ⋙ (dgModuleRestriction A D E F.op).onClosed ≅
      (dgModuleRestriction A D T (F.comp G).op).onClosed :=
  NatIso.ofComponents (fun M => (graphRestrictionCompositionIso A D E T F G).app M)
    (by
      intro M N f
      apply moduleMorphism_ext
      intro d
      simp only [Functor.comp_map, CategoryTheory.Functor.map_comp,
        dgModuleRestriction_map_eval, Iso.app_hom, graphRestrictionCompositionIso,
        NatIso.ofComponents_hom_app, moduleIsoMk_hom_eval, Iso.refl_hom]
      change (moduleEvaluation A T (G.obj (F.obj d))).map f ≫ 𝟙 _ =
        𝟙 _ ≫ (moduleEvaluation A T (G.obj (F.obj d))).map f
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

local instance graphRestrictionECompositionShift :
    (dgModuleRestriction A E T G.op).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A T E (dgModuleRestriction A E T G.op)
local instance graphRestrictionCompositeShift :
    (dgModuleRestriction A D T (F.comp G).op).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A T D (dgModuleRestriction A D T (F.comp G).op)

lemma graphRestrictionEnrichedCompositionIso_eval (M : ModuleCategory A T) (d : D) :
    (moduleEvaluation A D d).map
      ((graphRestrictionEnrichedCompositionIso A D E F T G).hom.app M) = 𝟙 _ := by
  exact moduleIsoMk_hom_eval A D _ _ d

instance graphRestrictionEnrichedCompositionIsoCommShift :
    NatTrans.CommShift (graphRestrictionEnrichedCompositionIso A D E F T G).hom ℤ where
  shift_comm s := by
    apply NatTrans.ext
    funext M
    apply moduleMorphism_ext
    intro d
    apply HomologicalComplex.hom_ext
    intro i
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      Functor.commShiftIso_comp_hom_app, CategoryTheory.Functor.map_comp,
      HomologicalComplex.comp_f, dgModuleRestriction_map_eval,
      graphRestrictionEnrichedCompositionIso_eval, HomologicalComplex.id_f]
    rw [graphRestrictionShift_hom_eval, graphRestrictionShift_hom_eval,
      graphRestrictionShift_hom_eval]
    change 𝟙 _ ≫ 𝟙 _ ≫
      ((moduleEvaluation A D d).map
        ((shiftFunctor (ModuleCategory A D) s).map
          ((graphRestrictionEnrichedCompositionIso A D E F T G).hom.app M))).f i = 𝟙 _ ≫ 𝟙 _
    rw [moduleShiftFunctor_eq]
    change 𝟙 _ ≫ 𝟙 _ ≫
      ((moduleEvaluation A D d).map
        (moduleShiftMap A D s
          ((graphRestrictionEnrichedCompositionIso A D E F T G).hom.app M))).f i = _
    rw [moduleShiftMap_eval, graphRestrictionEnrichedCompositionIso_eval]
    simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f,
      Category.id_comp]
    rfl
end SerrePositivity.DifferentialGraded
end

end GraphRestrictionShift

/-! ## GraphCompositionShift（旧 SerrePositivity/DifferentialGraded/Verdier/GraphCompositionShift.lean） -/

/-! # 既存の導来 graph 合成比較の shift 整合性 -/

@[expose] public section GraphCompositionShift
universe u v w t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

local instance graphCompositionDRestrictionShift :
    (dgModuleRestriction A D E F.op).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A E D (dgModuleRestriction A D E F.op)
local instance graphCompositionERestrictionShift :
    (dgModuleRestriction A E T G.op).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A T E (dgModuleRestriction A E T G.op)
local instance graphCompositionCompositeRestrictionShift :
    (dgModuleRestriction A D T (F.comp G).op).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A T D (dgModuleRestriction A D T (F.comp G).op)
local instance graphCompositionDerivedDRestrictionShift :
    (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F
local instance graphCompositionDerivedERestrictionShift :
    (dgDerivedRestriction A E T G).CommShift ℤ := dgDerivedRestrictionCommShift A E T G
local instance graphCompositionDerivedCompositeRestrictionShift :
    (dgDerivedRestriction A D T (F.comp G)).CommShift ℤ :=
  dgDerivedRestrictionCommShift A D T (F.comp G)

/-- 全 Hom の制限表示を使う、局所化前の整合的な合成比較。 -/
def graphRestrictionCompositionPreIso :
    moduleToDerived A T ⋙ (dgDerivedRestriction A E T G ⋙ dgDerivedRestriction A D E F) ≅
      moduleToDerived A T ⋙ dgDerivedRestriction A D T (F.comp G) :=
  (associator _ _ _).symm ≪≫
    isoWhiskerRight (eqToIso (dgDerivedRestriction_enriched_fac A E T G)) _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft _ (eqToIso (dgDerivedRestriction_enriched_fac A D E F)) ≪≫
    (associator _ _ _).symm ≪≫
    isoWhiskerRight (graphRestrictionEnrichedCompositionIso A D E F T G) _ ≪≫
    (eqToIso (dgDerivedRestriction_enriched_fac A D T (F.comp G))).symm

instance graphRestrictionCompositionPreIsoCommShift :
    NatTrans.CommShift (graphRestrictionCompositionPreIso A D E T F G).hom ℤ := by
  let := dgDerivedRestrictionFac_commShift A E T G
  let := dgDerivedRestrictionFac_commShift A D E F
  let := dgDerivedRestrictionFac_commShift A D T (F.comp G)
  unfold graphRestrictionCompositionPreIso
  simp only [Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom]
  infer_instance

lemma graphRestrictionCompositionPreIso_eq :
    (graphRestrictionCompositionPreIso A D E T F G).hom =
      whiskerLeft (moduleToDerived A T)
        (derivedGraphRestrictionCompositionIso A D E T F G).hom := by
  have he := (Localization.fullyFaithfulWhiskeringLeft
    (moduleToDerived A T) (moduleQuasiIso A T) (DerivedModuleCategory A D)).map_preimage
    (((associator _ _ _).symm ≪≫
      isoWhiskerRight (eqToIso (dgDerivedRestriction_fac A E T G)) _ ≪≫
      associator _ _ _ ≪≫
      isoWhiskerLeft _ (eqToIso (dgDerivedRestriction_fac A D E F)) ≪≫
      (associator _ _ _).symm ≪≫
      isoWhiskerRight (graphRestrictionCompositionIso A D E T F G) _ ≪≫
      (eqToIso (dgDerivedRestriction_fac A D T (F.comp G))).symm).hom)
  refine Eq.trans ?_ he.symm
  apply NatTrans.ext
  funext M
  simp only [graphRestrictionCompositionPreIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, NatTrans.comp_app, whiskerRight_app,
    whiskerLeft_app, associator_hom_app, associator_inv_app, eqToIso.hom, eqToIso.inv, eqToHom_app,
    eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

/-- 元の導来制限合成同型そのものが、固定した標準 shift と整合する。 -/
instance derivedGraphRestrictionCompositionIsoCommShift :
    NatTrans.CommShift (derivedGraphRestrictionCompositionIso A D E T F G).hom ℤ := by
  let := (Localization.fullyFaithfulWhiskeringLeft
    (moduleToDerived A T) (moduleQuasiIso A T) (DerivedModuleCategory A D)).faithful
  apply natTransCommShift_of_precomp (moduleToDerived A T) _ (hτ := ?_)
  rw [← graphRestrictionCompositionPreIso_eq]
  infer_instance

local instance graphCompositionDerivedDExtensionShift :
    (dgDerivedExtension A D E F).CommShift ℤ := dgDerivedExtensionCommShift A D E F
local instance graphCompositionDerivedEExtensionShift :
    (dgDerivedExtension A E T G).CommShift ℤ := dgDerivedExtensionCommShift A E T G
local instance graphCompositionDerivedCompositeExtensionShift :
    (dgDerivedExtension A D T (F.comp G)).CommShift ℤ :=
  dgDerivedExtensionCommShift A D T (F.comp G)

/-- 元の導来延長合成同型を保ったまま、随伴により固定した shift との整合性を得る。 -/
instance derivedGraphExtensionCompositionIsoCommShift :
    NatTrans.CommShift (derivedGraphExtensionCompositionIso A D E T F G).hom ℤ := by
  let := dgDerivedExtensionRestrictionAdjunction_commShift A D E F
  let := dgDerivedExtensionRestrictionAdjunction_commShift A E T G
  let := dgDerivedExtensionRestrictionAdjunction_commShift A D T (F.comp G)
  let := adjunctionOfNatIsoRightCommShift (M := ℤ)
    (dgDerivedExtensionRestrictionAdjunction A D T (F.comp G))
    (derivedGraphRestrictionCompositionIso A D E T F G).symm
  exact leftAdjointUniqCommShift (M := ℤ) _ _

/-- 合成比較は三角形関手への実際の自然同型も定める。 -/
def derivedGraphExtensionCompositionTriangleIso :=
  Functor.mapTriangleIso (derivedGraphExtensionCompositionIso A D E T F G)

end SerrePositivity.DifferentialGraded
end

end GraphCompositionShift
