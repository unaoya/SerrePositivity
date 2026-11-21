module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Adjunction.Basic
public import SerrePositivity.CategoryTheory.Adjunction.Comparison
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import SerrePositivity.CategoryTheory.Enriched.BaseChange
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
# 自由係数と閉テンソルによる写像随伴
-/

/-! # 自由パラメータ関手と右テンソルによる写像対象の随伴 -/

@[expose] public section MappingAdjunction
universe v₁ v₂ v₃ u₁ u₂ u₃ u₄ u₅

noncomputable section

namespace SerrePositivity.MonoidalMappingAdjunction

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
  {L : V ⥤ C} {R : C ⥤ V} (a : L ⊣ R)

/-- 右テンソルと自由パラメータの随伴を合成する。 -/
def adjunction (E : C) : L ⋙ tensorRight E ⊣ ihom E ⋙ R :=
  a.comp ((ihom.adjunction E).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight E))

/-- 合成随伴の転置を、通常の内部Homの転置と元の随伴で計算する。 -/
lemma homEquiv_formula (E : C) {X : V} {F : C} (g : L.obj X ⊗ E ⟶ F) :
    (adjunction a E).homEquiv X F g =
      a.homEquiv X ((ihom E).obj F) (curry ((β_ E (L.obj X)).hom ≫ g)) := by
  unfold adjunction
  rw [Adjunction.comp_homEquiv]
  change a.homEquiv X ((ihom E).obj F)
    (((ihom.adjunction E).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight E)).homEquiv
      (L.obj X) F g) = _
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  rfl

/-- 写像対象への転置はテンソルの固定因子の射に関して反変に自然。 -/
lemma homEquiv_pre {E E' : C} (f : E' ⟶ E) {X : V} {F : C}
    (g : L.obj X ⊗ E ⟶ F) :
    (adjunction a E').homEquiv X F (L.obj X ◁ f ≫ g) =
      (adjunction a E).homEquiv X F g ≫ R.map ((pre f).app F) := by
  rw [homEquiv_formula, homEquiv_formula]
  rw [← Category.assoc, ← BraidedCategory.braiding_naturality_left, Category.assoc,
    ← curry_pre_app]
  exact a.homEquiv_naturality_right _ _

/-- 比較で移した写像対象への転置の原変数に関する自然性の法則。 -/
def transportedPreLaw {E E' : C} (f : E' ⟶ E)
    {T T' : V ⥤ C} (e : L ⋙ tensorRight E ≅ T) (e' : L ⋙ tensorRight E' ≅ T')
    {X : V} {F : C} (t : T'.obj X ⟶ T.obj X) (g : T.obj X ⟶ F) : Prop :=
  ((adjunction a E').ofNatIsoLeft e').homEquiv X F (t ≫ g) =
    ((adjunction a E).ofNatIsoLeft e).homEquiv X F g ≫ R.map ((pre f).app F)

/-- テンソルの比較の自然性から、移送後の転置の原変数の自然性を得る。 -/
lemma transported_pre {E E' : C} (f : E' ⟶ E)
    {T T' : V ⥤ C} (e : L ⋙ tensorRight E ≅ T) (e' : L ⋙ tensorRight E' ≅ T')
    {X : V} {F : C} (t : T'.obj X ⟶ T.obj X) (g : T.obj X ⟶ F)
    (ht : L.obj X ◁ f ≫ e.hom.app X = e'.hom.app X ≫ t) :
    transportedPreLaw a f e e' t g := by
  unfold transportedPreLaw
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.homEquiv_ofNatIsoLeft_apply]
  rw [← Category.assoc, ← ht, Category.assoc, homEquiv_pre]

/-- Source naturality with the full postcomposed internal-Hom bifunctor. -/
lemma transported_pre_bifunctor {E E' : C} (f : E' ⟶ E)
    {T T' : V ⥤ C} (e : L ⋙ tensorRight E ≅ T) (e' : L ⋙ tensorRight E' ≅ T')
    {X : V} {F : C} (t : T'.obj X ⟶ T.obj X) (g : T.obj X ⟶ F)
    (ht : L.obj X ◁ f ≫ e.hom.app X = e'.hom.app X ≫ t) :
    ((adjunction a E').ofNatIsoLeft e').homEquiv X F (t ≫ g) =
      ((adjunction a E).ofNatIsoLeft e).homEquiv X F g ≫
        ((internalHom ⋙ (Functor.whiskeringRight C C V).obj R).map f.op).app F :=
  transported_pre a f e e' t g ht

/-- 移送後の逆転置の原変数の射に関する自然性の法則。 -/
def transportedUncurryPreLaw {E E' : C} (f : E' ⟶ E)
    {T T' : V ⥤ C} (e : L ⋙ tensorRight E ≅ T) (e' : L ⋙ tensorRight E' ≅ T')
    {X : V} {F : C} (t : T'.obj X ⟶ T.obj X) (g : X ⟶ R.obj ((ihom E).obj F)) : Prop :=
  (((adjunction a E').ofNatIsoLeft e').homEquiv X F).symm
      (g ≫ R.map ((pre f).app F)) =
    t ≫ (((adjunction a E).ofNatIsoLeft e).homEquiv X F).symm g

/-- 転置の自然性と相互逆性から、逆転置の原変数の自然性を得る。 -/
lemma transported_uncurry_pre {E E' : C} (f : E' ⟶ E)
    {T T' : V ⥤ C} (e : L ⋙ tensorRight E ≅ T) (e' : L ⋙ tensorRight E' ≅ T')
    {X : V} {F : C} (t : T'.obj X ⟶ T.obj X) (g : X ⟶ R.obj ((ihom E).obj F))
    (ht : L.obj X ◁ f ≫ e.hom.app X = e'.hom.app X ≫ t) :
    transportedUncurryPreLaw a f e e' t g := by
  unfold transportedUncurryPreLaw
  apply (((adjunction a E').ofNatIsoLeft e').homEquiv X F).injective
  rw [Equiv.apply_symm_apply]
  have h := transported_pre a f e e' t
    ((((adjunction a E).ofNatIsoLeft e).homEquiv X F).symm g) ht
  unfold transportedPreLaw at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

section

variable {P : Type u₃} [Category.{v₃} P] {J : P ⥤ V} {Q : V ⥤ P} (c : J ⊣ Q)

/-- 自由パラメータへの随伴も合成した転置の原変数の自然性。 -/
def compositeTransportedPreLaw {E E' : C} (f : E' ⟶ E)
    {T T' : V ⥤ C} (e : L ⋙ tensorRight E ≅ T) (e' : L ⋙ tensorRight E' ≅ T')
    {X : P} {F : C} (t : T'.obj (J.obj X) ⟶ T.obj (J.obj X))
    (g : T.obj (J.obj X) ⟶ F) : Prop :=
  AdjunctionCompositeNaturality.preLaw c ((adjunction a E).ofNatIsoLeft e)
    ((adjunction a E').ofNatIsoLeft e') t g (R.map ((pre f).app F))

/-- テンソルの比較の自然性から、合成随伴の原変数の自然性を得る。 -/
lemma composite_transported_pre {E E' : C} (f : E' ⟶ E)
    {T T' : V ⥤ C} (e : L ⋙ tensorRight E ≅ T) (e' : L ⋙ tensorRight E' ≅ T')
    {X : P} {F : C} (t : T'.obj (J.obj X) ⟶ T.obj (J.obj X))
    (g : T.obj (J.obj X) ⟶ F)
    (ht : L.obj (J.obj X) ◁ f ≫ e.hom.app (J.obj X) = e'.hom.app (J.obj X) ≫ t) :
    compositeTransportedPreLaw a c f e e' t g :=
  AdjunctionCompositeNaturality.pre c ((adjunction a E).ofNatIsoLeft e)
    ((adjunction a E').ofNatIsoLeft e') t g (R.map ((pre f).app F))
    (transported_pre a f e e' t g ht)

/-- 合成した写像対象の転置と別の同値を介して得る同値の原変数の自然性。 -/
def compositeDerivedPreLaw {E E' : C} (f : E' ⟶ E)
    {T T' : V ⥤ C} (e : L ⋙ tensorRight E ≅ T) (e' : L ⋙ tensorRight E' ≅ T')
    {X : P} {F : C} {Z : Type u₄} {Z' : Type u₅}
    (r : (T.obj (J.obj X) ⟶ F) ≃ Z) (r' : (T'.obj (J.obj X) ⟶ F) ≃ Z')
    (h : Z → Z') (y : X ⟶ Q.obj (R.obj ((ihom E).obj F))) : Prop :=
  AdjunctionCompositeNaturality.derivedPreLaw c ((adjunction a E).ofNatIsoLeft e)
    ((adjunction a E').ofNatIsoLeft e') r r' (R.map ((pre f).app F)) h y

/-- 比較と二つの転置の自然性から、導いたHom同値の原変数の自然性を得る。 -/
lemma composite_derived_pre {E E' : C} (f : E' ⟶ E)
    {T T' : V ⥤ C} (e : L ⋙ tensorRight E ≅ T) (e' : L ⋙ tensorRight E' ≅ T')
    {X : P} {F : C} {Z : Type u₄} {Z' : Type u₅}
    (r : (T.obj (J.obj X) ⟶ F) ≃ Z) (r' : (T'.obj (J.obj X) ⟶ F) ≃ Z')
    (t : T'.obj (J.obj X) ⟶ T.obj (J.obj X)) (h : Z → Z')
    (ht : L.obj (J.obj X) ◁ f ≫ e.hom.app (J.obj X) = e'.hom.app (J.obj X) ≫ t)
    (hr : ∀ k, r' (t ≫ k) = h (r k)) (y : X ⟶ Q.obj (R.obj ((ihom E).obj F))) :
    compositeDerivedPreLaw a c f e e' r r' h y :=
  AdjunctionCompositeNaturality.derived_pre c ((adjunction a E).ofNatIsoLeft e)
    ((adjunction a E').ofNatIsoLeft e') r r' t (R.map ((pre f).app F)) h
    (fun k => composite_transported_pre a c f e e' t k ht) hr y

end

end SerrePositivity.MonoidalMappingAdjunction
end

end MappingAdjunction


/-! # Parametrized mapping adjunctions from a transported tensor action -/

@[expose] public section MappingParametrizedAdjunction
universe v₁ v₂ u₁ u₂

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace SerrePositivity.MonoidalMappingAdjunction
variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
  {L : V ⥤ C} {R : C ⥤ V} (a : L ⊣ R)
  (H : V ⥤ C ⥤ C)
  (e : ∀ E, L ⋙ tensorRight E ≅ H.flip.obj E)
  (he : ∀ {E E' : C} (f : E' ⟶ E) (X : V),
    L.obj X ◁ f ≫ (e E).hom.app X =
      (e E').hom.app X ≫ (H.obj X).map f)

/-- A compatible family of transported tensor adjunctions is parametrized. -/
def transportedParametrizedAdjunction :
    H.flip ⊣₂ (MonoidalClosed.internalHom ⋙ (Functor.whiskeringRight C C V).obj R) := by
  refine ParametrizedAdjunction.mk' (fun E ↦ (adjunction a E).ofNatIsoLeft (e E)) ?_
  intro E E' f X F g
  exact transported_pre_bifunctor a f (e E') (e E) ((H.obj X).map f) g (he f X)

end SerrePositivity.MonoidalMappingAdjunction
end

end MappingParametrizedAdjunction
