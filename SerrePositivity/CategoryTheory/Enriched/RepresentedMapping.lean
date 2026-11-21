module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Adjunction.Basic
public import SerrePositivity.CategoryTheory.Adjunction.Comparison
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import SerrePositivity.CategoryTheory.Enriched.Transport
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
# Enriched.RepresentedMapping

## 概要
関連する圏論の構成と補題をまとめる。各構成の詳細は以下の元モジュールの説明を参照。

## 方針
元の宣言と証明を保持し、依存順に section を分けて配置する。

## 規約
公開宣言名・名前空間・宇宙変数の意味を変更しない。元の module docstring は各節に保存する。

## 使われ方
旧モジュールの利用元は `SerrePositivity.CategoryTheory.Enriched.RepresentedMapping` を直接 import する。
-/

/-! ## MappingAdjunction（旧 SerrePositivity/CategoryTheory/Monoidal/MappingAdjunction.lean） -/

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

/-! ## MappingUnitLaws（旧 SerrePositivity/CategoryTheory/Monoidal/MappingUnitLaws.lean） -/

/-! # 作用の表現性から得る写像対象の左単位の評価 -/

@[expose] public section MappingUnitLaws
universe v₁ v₂ u₁ u₂

namespace SerrePositivity.MappingUnitLaws

open CategoryTheory CategoryTheory.MonoidalCategory

variable {V : Type u₁} {D : Type u₂} [Category.{v₁} V] [Category.{v₂} D]
  [MonoidalCategory V] (H : V ⥤ D ⥤ D)

/-- 作用の値域を固定したパラメータ関手。 -/
abbrev parameterFunctor (E : D) : V ⥤ D where
  obj X := (H.obj X).obj E
  map f := (H.map f).app E
  map_id X := by rw [H.map_id]; rfl
  map_comp f g := by rw [H.map_comp]; rfl

variable (u : H.obj (𝟙_ V) ≅ 𝟭 D)

/-- 写像対象の左単位の評価を、作用の単位と結同比較から計算する。 -/
lemma left_unit_evaluation {P Q : V} {E F : D} (h : 𝟙_ V ⟶ P)
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ F)
    (b : (parameterFunctor H E).obj (P ⊗ Q) ⟶ (H.obj P).obj ((H.obj Q).obj E))
    (b₀ : (parameterFunctor H E).obj ((𝟙_ V) ⊗ Q) ⟶ (H.obj (𝟙_ V)).obj ((H.obj Q).obj E))
    (hb : (parameterFunctor H E).map (h ⊗ₘ 𝟙 Q) ≫ b = b₀ ≫ (H.map h).app ((H.obj Q).obj E))
    (hw : (H.map h).app F ≫ w = u.hom.app F)
    (hu : b₀ ≫ u.hom.app ((H.obj Q).obj E) = (parameterFunctor H E).map (λ_ Q).hom) :
    (parameterFunctor H E).map (h ⊗ₘ 𝟙 Q) ≫ b ≫ (H.obj P).map v ≫ w =
      (parameterFunctor H E).map (λ_ Q).hom ≫ v := by
  erw [← Category.assoc, ← Category.assoc, hb]
  simp only [Category.assoc]
  erw [← reassoc_of% ((H.map h).naturality v)]
  erw [hw, u.hom.naturality v, ← Category.assoc, hu]
  rfl

/-- 写像対象の右単位の評価を、作用の単位と結同比較から計算する。 -/
lemma right_unit_evaluation {P Q : V} {E F : D} (h : 𝟙_ V ⟶ Q)
    (v : (H.obj P).obj E ⟶ F) (w : (H.obj Q).obj E ⟶ E)
    (b : (parameterFunctor H E).obj (P ⊗ Q) ⟶ (H.obj P).obj ((H.obj Q).obj E))
    (b₀ : (parameterFunctor H E).obj (P ⊗ (𝟙_ V)) ⟶
      (H.obj P).obj ((H.obj (𝟙_ V)).obj E))
    (hb : (parameterFunctor H E).map (𝟙 P ⊗ₘ h) ≫ b =
      b₀ ≫ (H.obj P).map ((H.map h).app E))
    (hw : (H.map h).app E ≫ w = u.hom.app E)
    (hu : b₀ ≫ (H.obj P).map (u.hom.app E) = (parameterFunctor H E).map (ρ_ P).hom) :
    (parameterFunctor H E).map (𝟙 P ⊗ₘ h) ≫ b ≫ (H.obj P).map w ≫ v =
      (parameterFunctor H E).map (ρ_ P).hom ≫ v := by
  erw [← Category.assoc, ← Category.assoc, hb]
  simp only [Category.assoc]
  erw [← CategoryTheory.Functor.map_comp_assoc, hw, ← Category.assoc, hu]

end SerrePositivity.MappingUnitLaws

end MappingUnitLaws

/-! ## MappingParametrizedAdjunction（旧 SerrePositivity/CategoryTheory/Monoidal/MappingParametrizedAdjunction.lean） -/

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

/-! ## MappingAssociativity（旧 SerrePositivity/CategoryTheory/Monoidal/MappingAssociativity.lean） -/

/-! # 作用の五角形から得る写像対象の合成の結合性 -/

@[expose] public section MappingAssociativity
universe v₁ v₂ u₁ u₂

namespace SerrePositivity.MappingAssociativity

open CategoryTheory CategoryTheory.MonoidalCategory

variable {V : Type u₁} {D : Type u₂} [Category.{v₁} V] [Category.{v₂} D]
  [MonoidalCategory V] (H : V ⥤ D ⥤ D)
  (a : ∀ P Q : V, H.obj (P ⊗ Q) ≅ H.obj Q ⋙ H.obj P)

/-- 結同比較を通り、二つの評価を適用する射。 -/
def compositionEvaluation (P Q : V) {E F G : D}
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ G) :
    (H.obj (P ⊗ Q)).obj E ⟶ G :=
  (a P Q).hom.app E ≫ (H.obj P).map v ≫ w

/-- 二通りの反復合成を評価した射が等しいという法則。 -/
def associativityEvaluationLaw {P Q R S T : V} {E F G K : D}
    (m : P ⊗ Q ⟶ S) (n : Q ⊗ R ⟶ T)
    (v : (H.obj R).obj E ⟶ F)
    (z : (H.obj P).obj G ⟶ K) (s : (H.obj S).obj F ⟶ K)
    (t : (H.obj T).obj E ⟶ G) : Prop :=
  (H.map (m ⊗ₘ 𝟙 R)).app E ≫ compositionEvaluation H a S R v s =
    (H.map ((α_ P Q R).hom ≫ (𝟙 P ⊗ₘ n))).app E ≫
      compositionEvaluation H a P T t z

/-- 結同比較の自然性と五角形により、反復合成の評価は一致する。 -/
lemma associativity_evaluation {P Q R S T : V} {E F G K : D}
    (m : P ⊗ Q ⟶ S) (n : Q ⊗ R ⟶ T)
    (v : (H.obj R).obj E ⟶ F) (w : (H.obj Q).obj F ⟶ G)
    (z : (H.obj P).obj G ⟶ K) (s : (H.obj S).obj F ⟶ K)
    (t : (H.obj T).obj E ⟶ G)
    (hm : (H.map m).app F ≫ s = compositionEvaluation H a P Q w z)
    (hn : (H.map n).app E ≫ t = compositionEvaluation H a Q R v w)
    (hl : (H.map (m ⊗ₘ 𝟙 R)).app E ≫ (a S R).hom.app E =
      (a (P ⊗ Q) R).hom.app E ≫ (H.map m).app ((H.obj R).obj E))
    (hr : (H.map (𝟙 P ⊗ₘ n)).app E ≫ (a P T).hom.app E =
      (a P (Q ⊗ R)).hom.app E ≫ (H.obj P).map ((H.map n).app E))
    (hp : (H.map (α_ P Q R).hom).app E ≫ (a P (Q ⊗ R)).hom.app E ≫
      (H.obj P).map ((a Q R).hom.app E) =
        (a (P ⊗ Q) R).hom.app E ≫ (a P Q).hom.app ((H.obj R).obj E)) :
    associativityEvaluationLaw H a m n v z s t := by
  unfold associativityEvaluationLaw compositionEvaluation at *
  rw [H.map_comp, NatTrans.comp_app]
  rw [reassoc_of% hl, ← reassoc_of% ((H.map m).naturality v), hm]
  simp only [Category.assoc]
  rw [reassoc_of% ((a P Q).hom.naturality v)]
  rw [reassoc_of% hr]
  conv_rhs => rw [← CategoryTheory.Functor.map_comp_assoc, hn]
  rw [(H.obj P).map_comp, (H.obj P).map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hp]

/-- 評価の一致を転置して得る写像対象の結合則の等式。 -/
def representedAssociativityLaw {E F G K : D} {U : D ⥤ V}
    (adj : MappingUnitLaws.parameterFunctor H E ⊣ U)
    {P Q R S T : V} (m : P ⊗ Q ⟶ S) (n : Q ⊗ R ⟶ T)
    (v : (H.obj R).obj E ⟶ F) (z : (H.obj P).obj G ⟶ K)
    (s : (H.obj S).obj F ⟶ K) (t : (H.obj T).obj E ⟶ G) : Prop :=
  AdjunctionHomLaws.curryPreComparisonLaw adj
    (compositionEvaluation H a S R v s) (compositionEvaluation H a P T t z)
    (m ⊗ₘ 𝟙 R) ((α_ P Q R).hom ≫ (𝟙 P ⊗ₘ n))

/-- 表現性と反復合成の評価の一致から、写像対象の結合則を得る。 -/
lemma represented_associativity {E F G K : D} {U : D ⥤ V}
    (adj : MappingUnitLaws.parameterFunctor H E ⊣ U)
    {P Q R S T : V} (m : P ⊗ Q ⟶ S) (n : Q ⊗ R ⟶ T)
    (v : (H.obj R).obj E ⟶ F) (z : (H.obj P).obj G ⟶ K)
    (s : (H.obj S).obj F ⟶ K) (t : (H.obj T).obj E ⟶ G)
    (h : associativityEvaluationLaw H a m n v z s t) :
    representedAssociativityLaw H a adj m n v z s t :=
  AdjunctionHomLaws.curry_pre_comparison_of_evaluation adj
    (compositionEvaluation H a S R v s) (compositionEvaluation H a P T t z)
    (m ⊗ₘ 𝟙 R) ((α_ P Q R).hom ≫ (𝟙 P ⊗ₘ n)) h

end SerrePositivity.MappingAssociativity

end MappingAssociativity

/-! ## MappingArrowComposition（旧 SerrePositivity/CategoryTheory/Monoidal/MappingArrowComposition.lean） -/

/-! # 通常の射から写像対象の点への対応と合成 -/

@[expose] public section MappingArrowComposition
universe v₁ v₂ u₁ u₂

namespace SerrePositivity.MappingArrowComposition

open CategoryTheory CategoryTheory.MonoidalCategory

variable {V : Type u₁} {D : Type u₂} [Category.{v₁} V] [Category.{v₂} D]
  [MonoidalCategory V] (H : V ⥤ D ⥤ D)
  (a : ∀ P Q : V, H.obj (P ⊗ Q) ≅ H.obj Q ⋙ H.obj P)
  (u : H.obj (𝟙_ V) ≅ 𝟭 D)

/-- 二つの通常の射の点を合成した後の評価の法則。 -/
def arrowCompositionEvaluationLaw {P Q : V} {E F G : D}
    (f : E ⟶ F) (g : F ⟶ G) (p : 𝟙_ V ⟶ P) (q : 𝟙_ V ⟶ Q)
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ G) : Prop :=
  (H.map (p ⊗ₘ q)).app E ≫ MappingAssociativity.compositionEvaluation H a P Q v w =
    (H.map (λ_ (𝟙_ V)).hom).app E ≫ u.hom.app E ≫ f ≫ g

/-- 結同比較の自然性と作用の単位により、点の合成の評価は元の射の合成になる。 -/
lemma arrow_composition_evaluation {P Q : V} {E F G : D}
    (f : E ⟶ F) (g : F ⟶ G) (p : 𝟙_ V ⟶ P) (q : 𝟙_ V ⟶ Q)
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ G)
    (hv : (H.map q).app E ≫ v = u.hom.app E ≫ f)
    (hw : (H.map p).app F ≫ w = u.hom.app F ≫ g)
    (ha : (H.map (p ⊗ₘ q)).app E ≫ (a P Q).hom.app E =
      (a (𝟙_ V) (𝟙_ V)).hom.app E ≫ (H.map p).app ((H.obj (𝟙_ V)).obj E) ≫
        (H.obj P).map ((H.map q).app E))
    (hu : (a (𝟙_ V) (𝟙_ V)).hom.app E ≫ (H.obj (𝟙_ V)).map (u.hom.app E) =
      (H.map (ρ_ (𝟙_ V)).hom).app E) :
    arrowCompositionEvaluationLaw H a u f g p q v w := by
  unfold arrowCompositionEvaluationLaw MappingAssociativity.compositionEvaluation
  rw [reassoc_of% ha, ← CategoryTheory.Functor.map_comp_assoc, hv]
  rw [← reassoc_of% ((H.map p).naturality (u.hom.app E ≫ f))]
  rw [hw]
  rw [(H.obj (𝟙_ V)).map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (u.hom.naturality f)]
  change (a (𝟙_ V) (𝟙_ V)).hom.app E ≫ (H.obj (𝟙_ V)).map (u.hom.app E) ≫
    u.hom.app E ≫ f ≫ g = _
  rw [reassoc_of% hu, ← unitors_equal]

/-- 表現性を使った通常の射と写像対象の点の合成の一致の等式。 -/
def representedArrowCompositionLaw {E F G : D} {U : D ⥤ V}
    (adj : MappingUnitLaws.parameterFunctor H E ⊣ U)
    {P Q : V} (f : E ⟶ F) (g : F ⟶ G) (p : 𝟙_ V ⟶ P) (q : 𝟙_ V ⟶ Q)
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ G) : Prop :=
  (λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q) ≫
    adj.homEquiv _ G (MappingAssociativity.compositionEvaluation H a P Q v w) =
      AdjunctionHomLaws.comparisonHomEquiv adj (u.app E) G (f ≫ g)

/-- 点の合成の評価を表現性で戻すと、元の射の合成に対応する。 -/
lemma represented_arrow_composition {E F G : D} {U : D ⥤ V}
    (adj : MappingUnitLaws.parameterFunctor H E ⊣ U)
    {P Q : V} (f : E ⟶ F) (g : F ⟶ G) (p : 𝟙_ V ⟶ P) (q : 𝟙_ V ⟶ Q)
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ G)
    (h : arrowCompositionEvaluationLaw H a u f g p q v w) :
    representedArrowCompositionLaw H a u adj f g p q v w := by
  unfold representedArrowCompositionLaw
  rw [AdjunctionHomLaws.comparisonHomEquiv_apply]
  apply (cancel_epi (λ_ (𝟙_ V)).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  apply AdjunctionHomLaws.curry_pre_comparison_of_evaluation adj
  exact h

end SerrePositivity.MappingArrowComposition

end MappingArrowComposition

/-! ## RepresentedMappingEnrichment（旧 SerrePositivity/CategoryTheory/Monoidal/RepresentedMappingEnrichment.lean） -/

/-! # 作用の表現性による合成・単位から豊穣圏を構成する -/

@[expose] public section RepresentedMappingEnrichment
universe v₁ v₂ u₁ u₂

noncomputable section

namespace SerrePositivity.RepresentedMappingEnrichment

open CategoryTheory CategoryTheory.MonoidalCategory

variable {V : Type u₁} {D : Type u₂} [Category.{v₁} V] [Category.{v₂} D]
  [MonoidalCategory V]
  (H : V ⥤ D ⥤ D) (a : ∀ P Q : V, H.obj (P ⊗ Q) ≅ H.obj Q ⋙ H.obj P)
  (u : H.obj (𝟙_ V) ≅ 𝟭 D) (R : D → D ⥤ V)
  (adj : ∀ E, MappingUnitLaws.parameterFunctor H E ⊣ R E)

/-- 表現性を持つ作用の写像対象。 -/
def hom (E F : D) : V := (R E).obj F

/-- 作用の随伴の余単位による評価。 -/
def evaluation (E F : D) : (H.obj (hom R E F)).obj E ⟶ F := (adj E).counit.app F

/-- 作用の単位比較を転置した写像対象の単位。 -/
def unit (E : D) : 𝟙_ V ⟶ hom R E E := (adj E).homEquiv _ E (u.app E).hom

/-- 写像対象の単位の評価の等式。 -/
def unitEvaluationLaw (E : D) : Prop :=
  (H.map (unit H u R adj E)).app E ≫ evaluation H R adj E E = u.hom.app E

/-- 単位の評価は作用の単位比較。 -/
lemma unit_evaluation (E : D) : unitEvaluationLaw H u R adj E :=
  AdjunctionHomLaws.curry_evaluation (adj E) (u.app E).hom

/-- 二回の評価を作用の結同比較へ合成する。 -/
def compositionEvaluation (E F G : D) :
    (H.obj (hom R F G ⊗ hom R E F)).obj E ⟶ G :=
  MappingAssociativity.compositionEvaluation H a (hom R F G) (hom R E F)
    (evaluation H R adj E F) (evaluation H R adj F G)

/-- 二回の評価を転置した合成。 -/
def composition (E F G : D) : hom R F G ⊗ hom R E F ⟶ hom R E G :=
  (adj E).homEquiv _ G (compositionEvaluation H a R adj E F G)

/-- 合成の評価が二回の評価に一致するという法則。 -/
def compositionEvaluationLaw (E F G : D) : Prop :=
  (H.map (composition H a R adj E F G)).app E ≫ evaluation H R adj E G =
    compositionEvaluation H a R adj E F G

/-- 合成の評価は二回の評価に一致する。 -/
lemma composition_evaluation (E F G : D) : compositionEvaluationLaw H a R adj E F G :=
  AdjunctionHomLaws.curry_evaluation (adj E) (compositionEvaluation H a R adj E F G)

/-- 表現性から得た合成の左単位の評価の等式。 -/
def leftUnitEvaluationLaw (E F : D) : Prop :=
  (H.map (unit H u R adj F ⊗ₘ 𝟙 (hom R E F))).app E ≫
    compositionEvaluation H a R adj E F F =
  (H.map (λ_ (hom R E F)).hom).app E ≫ evaluation H R adj E F

/-- 表現性から得た合成の右単位の評価の等式。 -/
def rightUnitEvaluationLaw (E F : D) : Prop :=
  (H.map (𝟙 (hom R E F) ⊗ₘ unit H u R adj E)).app E ≫
    compositionEvaluation H a R adj E E F =
  (H.map (ρ_ (hom R E F)).hom).app E ≫ evaluation H R adj E F

/-- 作用の単位と自然性から写像対象の左単位の評価を計算する。 -/
lemma left_unit_evaluation (E F : D)
    (hn : (H.map (unit H u R adj F ⊗ₘ 𝟙 (hom R E F))).app E ≫
      (a (hom R F F) (hom R E F)).hom.app E =
      (a (𝟙_ V) (hom R E F)).hom.app E ≫
        (H.map (unit H u R adj F)).app ((H.obj (hom R E F)).obj E))
    (he : unitEvaluationLaw H u R adj F)
    (hu : (a (𝟙_ V) (hom R E F)).hom.app E ≫
      u.hom.app ((H.obj (hom R E F)).obj E) = (H.map (λ_ (hom R E F)).hom).app E) :
    leftUnitEvaluationLaw H a u R adj E F :=
  MappingUnitLaws.left_unit_evaluation H u (unit H u R adj F)
    (evaluation H R adj E F) (evaluation H R adj F F)
    ((a (hom R F F) (hom R E F)).hom.app E)
    ((a (𝟙_ V) (hom R E F)).hom.app E) hn he hu

/-- 作用の単位と自然性から写像対象の右単位の評価を計算する。 -/
lemma right_unit_evaluation (E F : D)
    (hn : (H.map (𝟙 (hom R E F) ⊗ₘ unit H u R adj E)).app E ≫
      (a (hom R E F) (hom R E E)).hom.app E =
      (a (hom R E F) (𝟙_ V)).hom.app E ≫
        (H.obj (hom R E F)).map ((H.map (unit H u R adj E)).app E))
    (he : unitEvaluationLaw H u R adj E)
    (hu : (a (hom R E F) (𝟙_ V)).hom.app E ≫
      (H.obj (hom R E F)).map (u.hom.app E) = (H.map (ρ_ (hom R E F)).hom).app E) :
    rightUnitEvaluationLaw H a u R adj E F :=
  MappingUnitLaws.right_unit_evaluation H u (unit H u R adj E)
    (evaluation H R adj E F) (evaluation H R adj E E)
    ((a (hom R E F) (hom R E E)).hom.app E)
    ((a (hom R E F) (𝟙_ V)).hom.app E) hn he hu

/-- 表現性から得た合成の左単位則。 -/
def leftUnitLaw (E F : D) : Prop :=
  AdjunctionHomLaws.curryPreEqualityLaw (adj E) (compositionEvaluation H a R adj E F F)
    (unit H u R adj F ⊗ₘ 𝟙 (hom R E F)) (λ_ (hom R E F)).hom

/-- 表現性から得た合成の右単位則。 -/
def rightUnitLaw (E F : D) : Prop :=
  AdjunctionHomLaws.curryPreEqualityLaw (adj E) (compositionEvaluation H a R adj E E F)
    (𝟙 (hom R E F) ⊗ₘ unit H u R adj E) (ρ_ (hom R E F)).hom

/-- 評価から写像対象の左単位則を得る。 -/
lemma left_unit (E F : D) (h : leftUnitEvaluationLaw H a u R adj E F) :
    leftUnitLaw H a u R adj E F :=
  AdjunctionHomLaws.curry_pre_eq_of_evaluation (adj E) (compositionEvaluation H a R adj E F F)
    (unit H u R adj F ⊗ₘ 𝟙 (hom R E F)) (λ_ (hom R E F)).hom h

/-- 評価から写像対象の右単位則を得る。 -/
lemma right_unit (E F : D) (h : rightUnitEvaluationLaw H a u R adj E F) :
    rightUnitLaw H a u R adj E F :=
  AdjunctionHomLaws.curry_pre_eq_of_evaluation (adj E) (compositionEvaluation H a R adj E E F)
    (𝟙 (hom R E F) ⊗ₘ unit H u R adj E) (ρ_ (hom R E F)).hom h

/-- 表現性から得た反復合成の評価の一致。 -/
def associativityEvaluationLaw (E F G K : D) : Prop :=
  MappingAssociativity.associativityEvaluationLaw H a
    (composition H a R adj F G K) (composition H a R adj E F G)
    (evaluation H R adj E F) (evaluation H R adj G K)
    (evaluation H R adj F K) (evaluation H R adj E G)

/-- 自然性と五角形から反復合成の評価の一致を得る。 -/
lemma associativity_evaluation (E F G K : D)
    (hl : (H.map (composition H a R adj F G K ⊗ₘ 𝟙 (hom R E F))).app E ≫
      (a (hom R F K) (hom R E F)).hom.app E =
      (a (hom R G K ⊗ hom R F G) (hom R E F)).hom.app E ≫
        (H.map (composition H a R adj F G K)).app ((H.obj (hom R E F)).obj E))
    (hr : (H.map (𝟙 (hom R G K) ⊗ₘ composition H a R adj E F G)).app E ≫
      (a (hom R G K) (hom R E G)).hom.app E =
      (a (hom R G K) (hom R F G ⊗ hom R E F)).hom.app E ≫
        (H.obj (hom R G K)).map ((H.map (composition H a R adj E F G)).app E))
    (hp : (H.map (α_ (hom R G K) (hom R F G) (hom R E F)).hom).app E ≫
      (a (hom R G K) (hom R F G ⊗ hom R E F)).hom.app E ≫
        (H.obj (hom R G K)).map ((a (hom R F G) (hom R E F)).hom.app E) =
      (a (hom R G K ⊗ hom R F G) (hom R E F)).hom.app E ≫
        (a (hom R G K) (hom R F G)).hom.app ((H.obj (hom R E F)).obj E)) :
    associativityEvaluationLaw H a R adj E F G K :=
  MappingAssociativity.associativity_evaluation H a
    (composition H a R adj F G K) (composition H a R adj E F G)
    (evaluation H R adj E F) (evaluation H R adj F G) (evaluation H R adj G K)
    (evaluation H R adj F K) (evaluation H R adj E G)
    (composition_evaluation H a R adj F G K) (composition_evaluation H a R adj E F G) hl hr hp

/-- 表現性から得た合成の結合則。 -/
def associativityLaw (E F G K : D) : Prop :=
  MappingAssociativity.representedAssociativityLaw H a (adj E)
    (composition H a R adj F G K) (composition H a R adj E F G)
    (evaluation H R adj E F) (evaluation H R adj G K)
    (evaluation H R adj F K) (evaluation H R adj E G)

/-- 反復合成の評価の一致から写像対象の結合則を得る。 -/
lemma associativity (E F G K : D) (h : associativityEvaluationLaw H a R adj E F G K) :
    associativityLaw H a R adj E F G K :=
  MappingAssociativity.represented_associativity H a (adj E)
    (composition H a R adj F G K) (composition H a R adj E F G)
    (evaluation H R adj E F) (evaluation H R adj G K)
    (evaluation H R adj F K) (evaluation H R adj E G) h

/-- 通常の射と単位から写像対象への射の同値。 -/
def arrowEquiv (E F : D) : (E ⟶ F) ≃ (𝟙_ V ⟶ hom R E F) :=
  AdjunctionHomLaws.comparisonHomEquiv (adj E) (u.app E) F

/-- 通常の射に対応する写像対象の点。 -/
def arrow {E F : D} (f : E ⟶ F) : 𝟙_ V ⟶ hom R E F := arrowEquiv H u R adj E F f

/-- 恒等射と写像対象の単位の対応。 -/
def arrowIdentityLaw (E : D) : Prop :=
  AdjunctionHomLaws.comparisonHomIdentityLaw (adj E) (u.app E)

/-- 恒等射は写像対象の単位に対応する。 -/
lemma arrow_identity (E : D) : arrowIdentityLaw H u R adj E :=
  AdjunctionHomLaws.comparisonHomEquiv_id (adj E) (u.app E)

/-- 通常の射の合成と写像対象の点の合成の対応。 -/
def arrowCompositionLaw {E F G : D} (f : E ⟶ F) (g : F ⟶ G) : Prop :=
  MappingArrowComposition.representedArrowCompositionLaw H a u (adj E)
    f g (arrow H u R adj g) (arrow H u R adj f)
    (evaluation H R adj E F) (evaluation H R adj F G)

variable [BraidedCategory V]

/-- 作用の表現性による写像対象の合成を通常の因子順の豊穣圏へまとめる。 -/
@[instance_reducible]
def enrichedCategory (hl : ∀ E F, leftUnitLaw H a u R adj E F)
    (hr : ∀ E F, rightUnitLaw H a u R adj E F)
    (ha : ∀ E F G K, associativityLaw H a R adj E F G K) : EnrichedCategory V D := by
  apply ReverseComposition.enrichedCategory D (hom R) (unit H u R adj)
    (composition H a R adj) hl hr
  intro W X Y Z
  have h := ha W X Y Z
  change (composition H a R adj X Y Z ⊗ₘ 𝟙 (hom R W X)) ≫
    composition H a R adj W X Z =
    ((α_ (hom R Y Z) (hom R X Y) (hom R W X)).hom ≫
      (𝟙 (hom R Y Z) ⊗ₘ composition H a R adj W X Y)) ≫
        composition H a R adj W Y Z at h
  simpa only [Category.assoc] using h

/-- 豊穣構造の単位は構成した単位。 -/
lemma enrichedCategory_id (hl : ∀ E F, leftUnitLaw H a u R adj E F)
    (hr : ∀ E F, rightUnitLaw H a u R adj E F)
    (ha : ∀ E F G K, associativityLaw H a R adj E F G K) (E : D) :
    (enrichedCategory H a u R adj hl hr ha).id E = unit H u R adj E := rfl

/-- 豊穣構造の合成は構成した合成の因子を交換したもの。 -/
lemma enrichedCategory_comp (hl : ∀ E F, leftUnitLaw H a u R adj E F)
    (hr : ∀ E F, rightUnitLaw H a u R adj E F)
    (ha : ∀ E F G K, associativityLaw H a R adj E F G K) (E F G : D) :
    (enrichedCategory H a u R adj hl hr ha).comp E F G =
      ReverseComposition.reverse (composition H a R adj E F G) := rfl

/-- 表現性による豊穣構造を既存の通常の圏構造と接続する。 -/
@[instance_reducible]
def ordinaryCategory (hl : ∀ E F, leftUnitLaw H a u R adj E F)
    (hr : ∀ E F, rightUnitLaw H a u R adj E F)
    (ha : ∀ E F G K, associativityLaw H a R adj E F G K)
    (hi : ∀ E, arrowIdentityLaw H u R adj E)
    (hc : ∀ {E F G} (f : E ⟶ F) (g : F ⟶ G), arrowCompositionLaw H a u R adj f g) :
    EnrichedOrdinaryCategory V D where
  toEnrichedCategory := enrichedCategory H a u R adj hl hr ha
  homEquiv := arrowEquiv H u R adj _ _
  homEquiv_id E := hi E
  homEquiv_comp f g := by
    apply Eq.symm
    apply ReverseComposition.points
    exact hc f g

end SerrePositivity.RepresentedMappingEnrichment
end

end RepresentedMappingEnrichment

/-! ## MappingWhiskering（旧 SerrePositivity/CategoryTheory/Monoidal/MappingWhiskering.lean） -/

/-! # Evaluation of composition with an ordinary arrow

One ordinary arrow and one arbitrary mapping-object parameter suffice to recover
mapping functoriality. These laws do not assume that unit-valued points detect
all morphisms of the enriching category.
-/

@[expose] public section MappingWhiskering
universe v₁ v₂ u₁ u₂

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace SerrePositivity.MappingWhiskering
variable {V : Type u₁} {D : Type u₂} [Category.{v₁} V] [Category.{v₂} D]
  [MonoidalCategory V] (H : V ⥤ D ⥤ D)
  (a : ∀ P Q : V, H.obj (P ⊗ Q) ≅ H.obj Q ⋙ H.obj P)
  (u : H.obj (𝟙_ V) ≅ 𝟭 D)

/-- Evaluate a composition whose final arrow is an ordinary arrow. -/
lemma post_evaluation {P Q : V} {E F G : D} (p : 𝟙_ V ⟶ P) (g : F ⟶ G)
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ G)
    (hp : (H.map p).app F ≫ w = u.hom.app F ≫ g)
    (hn : (H.map (p ⊗ₘ 𝟙 Q)).app E ≫ (a P Q).hom.app E =
      (a (𝟙_ V) Q).hom.app E ≫ (H.map p).app ((H.obj Q).obj E))
    (hu : (a (𝟙_ V) Q).hom.app E ≫ u.hom.app ((H.obj Q).obj E) =
      (H.map (λ_ Q).hom).app E) :
    (H.map (p ⊗ₘ 𝟙 Q)).app E ≫
        MappingAssociativity.compositionEvaluation H a P Q v w =
      (H.map (λ_ Q).hom).app E ≫ v ≫ g := by
  unfold MappingAssociativity.compositionEvaluation
  rw [reassoc_of% hn, ← reassoc_of% ((H.map p).naturality v), hp]
  rw [reassoc_of% (u.hom.naturality v), reassoc_of% hu]

/-- Evaluate a composition whose initial arrow is an ordinary arrow. -/
lemma pre_evaluation {P Q : V} {E F G : D} (p : 𝟙_ V ⟶ Q) (f : E ⟶ F)
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ G)
    (hp : (H.map p).app E ≫ v = u.hom.app E ≫ f)
    (hn : (H.map (𝟙 P ⊗ₘ p)).app E ≫ (a P Q).hom.app E =
      (a P (𝟙_ V)).hom.app E ≫ (H.obj P).map ((H.map p).app E))
    (hu : (a P (𝟙_ V)).hom.app E ≫ (H.obj P).map (u.hom.app E) =
      (H.map (ρ_ P).hom).app E) :
    (H.map (𝟙 P ⊗ₘ p)).app E ≫
        MappingAssociativity.compositionEvaluation H a P Q v w =
      (H.map (ρ_ P).hom).app E ≫ (H.obj P).map f ≫ w := by
  unfold MappingAssociativity.compositionEvaluation
  rw [reassoc_of% hn, ← Functor.map_comp_assoc, hp, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hu]

variable (R : D → D ⥤ V)
  (adj : ∀ E, MappingUnitLaws.parameterFunctor H E ⊣ R E)
open RepresentedMappingEnrichment

/-- Composition with the point of an ordinary arrow is the existing right
adjoint's map, on the entire mapping object. -/
lemma post_composition {E F G : D} (g : F ⟶ G)
    (hn : (H.map (arrow H u R adj g ⊗ₘ 𝟙 (hom R E F))).app E ≫
      (a (hom R F G) (hom R E F)).hom.app E =
      (a (𝟙_ V) (hom R E F)).hom.app E ≫
        (H.map (arrow H u R adj g)).app ((H.obj (hom R E F)).obj E))
    (hu : (a (𝟙_ V) (hom R E F)).hom.app E ≫
      u.hom.app ((H.obj (hom R E F)).obj E) =
        (H.map (λ_ (hom R E F)).hom).app E) :
    (λ_ (hom R E F)).inv ≫ arrow H u R adj g ▷ hom R E F ≫
      composition H a R adj E F G = (R E).map g := by
  rw [← Category.assoc]
  apply AdjunctionHomLaws.curry_pre_eq_of_evaluation (adj E)
    (compositionEvaluation H a R adj E F G)
    ((λ_ (hom R E F)).inv ≫ arrow H u R adj g ▷ hom R E F) ((R E).map g)
  change (H.map ((λ_ (hom R E F)).inv ≫ arrow H u R adj g ▷ hom R E F)).app E ≫
    compositionEvaluation H a R adj E F G =
      (H.map ((R E).map g)).app E ≫ evaluation H R adj E G
  have hp : (H.map (arrow H u R adj g)).app F ≫ evaluation H R adj F G =
      u.hom.app F ≫ g :=
    AdjunctionHomLaws.comparison_evaluation (adj F) (u.app F) g
  have he := post_evaluation H a u (arrow H u R adj g) g
    (evaluation H R adj E F) (evaluation H R adj F G) hp hn hu
  rw [H.map_comp, NatTrans.comp_app, Category.assoc]
  rw [← tensorHom_id (arrow H u R adj g) (hom R E F)]
  change (H.map (λ_ (hom R E F)).inv).app E ≫
    (H.map (arrow H u R adj g ⊗ₘ 𝟙 (hom R E F))).app E ≫
      compositionEvaluation H a R adj E F G = _
  change (H.map (arrow H u R adj g ⊗ₘ 𝟙 (hom R E F))).app E ≫
    compositionEvaluation H a R adj E F G =
      (H.map (λ_ (hom R E F)).hom).app E ≫ evaluation H R adj E F ≫ g at he
  rw [he]
  have hi : (H.map (λ_ (hom R E F)).inv).app E ≫
      (H.map (λ_ (hom R E F)).hom).app E = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← H.map_comp, Iso.inv_hom_id, H.map_id]
    rfl
  rw [← Category.assoc, ← Category.assoc, hi, Category.id_comp]
  exact ((adj E).counit.naturality g).symm

/-- Composition with an ordinary initial arrow is the transpose of precomposition
by its action, at arbitrary mapping-object parameters. -/
lemma pre_composition {E F G : D} (f : E ⟶ F)
    (hn : (H.map (𝟙 (hom R F G) ⊗ₘ arrow H u R adj f)).app E ≫
      (a (hom R F G) (hom R E F)).hom.app E =
      (a (hom R F G) (𝟙_ V)).hom.app E ≫
        (H.obj (hom R F G)).map ((H.map (arrow H u R adj f)).app E))
    (hu : (a (hom R F G) (𝟙_ V)).hom.app E ≫
      (H.obj (hom R F G)).map (u.hom.app E) =
        (H.map (ρ_ (hom R F G)).hom).app E) :
    (ρ_ (hom R F G)).inv ≫ hom R F G ◁ arrow H u R adj f ≫
      composition H a R adj E F G =
        (adj E).homEquiv (hom R F G) G
          ((H.obj (hom R F G)).map f ≫ evaluation H R adj F G) := by
  rw [← Category.assoc]
  conv_rhs => rw [← Category.id_comp ((adj E).homEquiv (hom R F G) G
    ((H.obj (hom R F G)).map f ≫ evaluation H R adj F G))]
  apply AdjunctionHomLaws.curry_pre_comparison_of_evaluation (adj E)
    (compositionEvaluation H a R adj E F G)
    ((H.obj (hom R F G)).map f ≫ evaluation H R adj F G)
    ((ρ_ (hom R F G)).inv ≫ hom R F G ◁ arrow H u R adj f) (𝟙 _)
  change (H.map ((ρ_ (hom R F G)).inv ≫ hom R F G ◁ arrow H u R adj f)).app E ≫
    compositionEvaluation H a R adj E F G =
      (H.map (𝟙 (hom R F G))).app E ≫
        (H.obj (hom R F G)).map f ≫ evaluation H R adj F G
  have hp : (H.map (arrow H u R adj f)).app E ≫ evaluation H R adj E F =
      u.hom.app E ≫ f :=
    AdjunctionHomLaws.comparison_evaluation (adj E) (u.app E) f
  have he := pre_evaluation H a u (arrow H u R adj f) f
    (evaluation H R adj E F) (evaluation H R adj F G) hp hn hu
  change (H.map (𝟙 (hom R F G) ⊗ₘ arrow H u R adj f)).app E ≫
    compositionEvaluation H a R adj E F G =
      (H.map (ρ_ (hom R F G)).hom).app E ≫
        (H.obj (hom R F G)).map f ≫ evaluation H R adj F G at he
  rw [H.map_comp, NatTrans.comp_app, Category.assoc,
    ← id_tensorHom (hom R F G) (arrow H u R adj f), he]
  have hi : (H.map (ρ_ (hom R F G)).inv).app E ≫
      (H.map (ρ_ (hom R F G)).hom).app E = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← H.map_comp, Iso.inv_hom_id, H.map_id]
    rfl
  rw [← Category.assoc, ← Category.assoc, hi, H.map_id]
  simp only [NatTrans.id_app, Category.id_comp]

section Enriched
variable [BraidedCategory V]
  (hl : ∀ E F, leftUnitLaw H a u R adj E F)
  (hr : ∀ E F, rightUnitLaw H a u R adj E F)
  (ha : ∀ E F G K, associativityLaw H a R adj E F G K)
  (hi : ∀ E, arrowIdentityLaw H u R adj E)
  (hc : ∀ {E F G} (f : E ⟶ F) (g : F ⟶ G), arrowCompositionLaw H a u R adj f g)

lemma enriched_post {E F G : D} (g : F ⟶ G)
    (hn : (H.map (arrow H u R adj g ⊗ₘ 𝟙 (hom R E F))).app E ≫
      (a (hom R F G) (hom R E F)).hom.app E =
      (a (𝟙_ V) (hom R E F)).hom.app E ≫
        (H.map (arrow H u R adj g)).app ((H.obj (hom R E F)).obj E))
    (hu : (a (𝟙_ V) (hom R E F)).hom.app E ≫
      u.hom.app ((H.obj (hom R E F)).obj E) = (H.map (λ_ (hom R E F)).hom).app E) :
    let : EnrichedOrdinaryCategory V D := ordinaryCategory H a u R adj hl hr ha hi hc
    eHomWhiskerLeft V E g = (R E).map g := by
  let : EnrichedOrdinaryCategory V D := ordinaryCategory H a u R adj hl hr ha hi hc
  change (ρ_ (hom R E F)).inv ≫ hom R E F ◁ arrow H u R adj g ≫
    (β_ _ _).hom ≫ composition H a R adj E F G = _
  rw [BraidedCategory.braiding_naturality_right_assoc,
    ← Category.assoc, rightUnitor_inv_braiding]
  exact post_composition H a u R adj g hn hu

lemma enriched_pre {E F G : D} (f : E ⟶ F)
    (hn : (H.map (𝟙 (hom R F G) ⊗ₘ arrow H u R adj f)).app E ≫
      (a (hom R F G) (hom R E F)).hom.app E =
      (a (hom R F G) (𝟙_ V)).hom.app E ≫
        (H.obj (hom R F G)).map ((H.map (arrow H u R adj f)).app E))
    (hu : (a (hom R F G) (𝟙_ V)).hom.app E ≫
      (H.obj (hom R F G)).map (u.hom.app E) = (H.map (ρ_ (hom R F G)).hom).app E) :
    let : EnrichedOrdinaryCategory V D := ordinaryCategory H a u R adj hl hr ha hi hc
    eHomWhiskerRight V f G = (adj E).homEquiv (hom R F G) G
      ((H.obj (hom R F G)).map f ≫ evaluation H R adj F G) := by
  let : EnrichedOrdinaryCategory V D := ordinaryCategory H a u R adj hl hr ha hi hc
  change (λ_ (hom R F G)).inv ≫ arrow H u R adj f ▷ hom R F G ≫
    (β_ _ _).hom ≫ composition H a R adj E F G = _
  rw [BraidedCategory.braiding_naturality_left_assoc,
    ← Category.assoc, leftUnitor_inv_braiding]
  exact pre_composition H a u R adj f hn hu
end Enriched

end SerrePositivity.MappingWhiskering
end

end MappingWhiskering

/-! ## RepresentedHomFunctor（旧 SerrePositivity/CategoryTheory/Monoidal/RepresentedHomFunctor.lean） -/

/-! # The Hom functor of a represented ordinary enrichment

The proof is performed with abstract action and adjunction data. Applications
need not normalize concrete chosen adjunction records in the kernel.
-/

@[expose] public section RepresentedHomFunctor
universe v₁ v₂ u₁ u₂

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
namespace SerrePositivity.RepresentedHomFunctor
open RepresentedMappingEnrichment
variable {V : Type u₁} {D : Type u₂} [Category.{v₁} V] [Category.{v₂} D]
  [MonoidalCategory V] [BraidedCategory V]
  (H : V ⥤ D ⥤ D) (a : ∀ P Q : V, H.obj (P ⊗ Q) ≅ H.obj Q ⋙ H.obj P)
  (u : H.obj (𝟙_ V) ≅ 𝟭 D) (R : D → D ⥤ V)
  (adj : ∀ E, MappingUnitLaws.parameterFunctor H E ⊣ R E)
  (hl : ∀ E F, leftUnitLaw H a u R adj E F)
  (hr : ∀ E F, rightUnitLaw H a u R adj E F)
  (ha : ∀ E F G K, associativityLaw H a R adj E F G K)
  (hi : ∀ E, arrowIdentityLaw H u R adj E)
  (hc : ∀ {E F G} (f : E ⟶ F) (g : F ⟶ G), arrowCompositionLaw H a u R adj f g)
  (hL : ∀ {P P' : V} (p : P ⟶ P') (Q : V) (E : D),
    (H.map (p ⊗ₘ 𝟙 Q)).app E ≫ (a P' Q).hom.app E =
      (a P Q).hom.app E ≫ (H.map p).app ((H.obj Q).obj E))
  (hR : ∀ (P : V) {Q Q' : V} (q : Q ⟶ Q') (E : D),
    (H.map (𝟙 P ⊗ₘ q)).app E ≫ (a P Q').hom.app E =
      (a P Q).hom.app E ≫ (H.obj P).map ((H.map q).app E))
  (huL : ∀ (P : V) (E : D), (a (𝟙_ V) P).hom.app E ≫
    u.hom.app ((H.obj P).obj E) = (H.map (λ_ P).hom).app E)
  (huR : ∀ (P : V) (E : D), (a P (𝟙_ V)).hom.app E ≫
    (H.obj P).map (u.hom.app E) = (H.map (ρ_ P).hom).app E)
  (B : Dᵒᵖ ⥤ D ⥤ V) (e : ∀ E, R E ≅ B.obj (op E))
  (hn : ∀ {E F : D} (f : E ⟶ F) (X : V) (G : D) (g : (H.obj X).obj F ⟶ G),
    (adj E).homEquiv X G ((H.obj X).map f ≫ g) ≫ (e E).hom.app G =
      (adj F).homEquiv X G g ≫ (e F).hom.app G ≫ (B.map f.op).app G)

def homFunctorIso :
    let : EnrichedOrdinaryCategory V D := ordinaryCategory H a u R adj hl hr ha hi hc
    eHomFunctor V D ≅ B := by
  let : EnrichedOrdinaryCategory V D := ordinaryCategory H a u R adj hl hr ha hi hc
  have hpost (E : D) {F G : D} (g : F ⟶ G) : eHomWhiskerLeft V E g = (R E).map g :=
    MappingWhiskering.enriched_post H a u R adj hl hr ha hi hc g
      (hL _ _ _) (huL _ _)
  have hpre {E F : D} (f : E ⟶ F) (G : D) :
      eHomWhiskerRight V f G ≫ (e E).hom.app G = (e F).hom.app G ≫ (B.map f.op).app G := by
    rw [MappingWhiskering.enriched_pre H a u R adj hl hr ha hi hc f (hR _ _ _) (huR _ _)]
    have he : (adj F).homEquiv (hom R F G) G (evaluation H R adj F G) = 𝟙 _ := by
      exact ((adj F).homEquiv _ G).eq_symm_apply.mp ((adj F).homEquiv_symm_id G).symm
    simpa only [he, Category.id_comp] using hn f (hom R F G) G (evaluation H R adj F G)
  refine NatIso.ofComponents (fun E ↦ NatIso.ofComponents (fun F ↦ (e E.unop).app F) ?_) ?_
  · intro F G g
    change eHomWhiskerLeft V E.unop g ≫ (e E.unop).hom.app G =
      (e E.unop).hom.app F ≫ (B.obj E).map g
    rw [hpost]
    exact (e E.unop).hom.naturality g
  · intro E F f
    apply NatTrans.ext
    funext G
    exact hpre f.unop G

/-- A parametrized adjunction supplies the contravariant naturality automatically. -/
def homFunctorIso_ofParametrized
    (adj₂ : H.flip ⊣₂ B)
    (hl' : ∀ E F, leftUnitLaw H a u (fun E ↦ B.obj (op E)) adj₂.adj E F)
    (hr' : ∀ E F, rightUnitLaw H a u (fun E ↦ B.obj (op E)) adj₂.adj E F)
    (ha' : ∀ E F G K, associativityLaw H a (fun E ↦ B.obj (op E)) adj₂.adj E F G K)
    (hi' : ∀ E, arrowIdentityLaw H u (fun E ↦ B.obj (op E)) adj₂.adj E)
    (hc' : ∀ {E F G} (f : E ⟶ F) (g : F ⟶ G),
      arrowCompositionLaw H a u (fun E ↦ B.obj (op E)) adj₂.adj f g) :
    let : EnrichedOrdinaryCategory V D := ordinaryCategory H a u
      (fun E ↦ B.obj (op E)) adj₂.adj hl' hr' ha' hi' hc'
    eHomFunctor V D ≅ B := by
  apply homFunctorIso H a u (fun E ↦ B.obj (op E)) adj₂.adj
    hl' hr' ha' hi' hc' hL hR huL huR B (fun _ ↦ Iso.refl _)
  intro E F f X G g
  simp only [Iso.refl_hom, NatTrans.id_app, Category.comp_id, Category.id_comp]
  change adj₂.homEquiv ((H.flip.map f).app X ≫ g) =
    adj₂.homEquiv g ≫ (B.map f.op).app G
  exact adj₂.homEquiv_naturality_one (X₁ := E) (Y₁ := F) (X₂ := X) (X₃ := G) f g

end SerrePositivity.RepresentedHomFunctor
end

end RepresentedHomFunctor
