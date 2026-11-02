module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Whiskering

/-!
# Adjunction.Comparison

## 概要
関連する圏論の構成と補題をまとめる。各構成の詳細は以下の元モジュールの説明を参照。

## 方針
元の宣言と証明を保持し、依存順に section を分けて配置する。

## 規約
公開宣言名・名前空間・宇宙変数の意味を変更しない。元の module docstring は各節に保存する。

## 使われ方
旧モジュールの利用元は `SerrePositivity.CategoryTheory.Adjunction.Comparison` を直接 import する。
-/

/-! ## ActionComparisonAdjunction（旧 SerrePositivity/CategoryTheory/Monoidal/ActionComparisonAdjunction.lean） -/

/-! # 左随伴の比較を右随伴へ移す -/

@[expose] public section ActionComparisonAdjunction
universe v w u u'

noncomputable section

namespace SerrePositivity.ActionComparisonAdjunction

open CategoryTheory

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{w} D]
  {L L' : C ⥤ D} {R R' : D ⥤ C}
  (a : L ⊣ R) (b : L' ⊣ R') (e : L ≅ L')

/-- 左随伴の自然同型と右随伴の一意性から得る右随伴の自然同型。 -/
def rightIso : R ≅ R' := (a.ofNatIsoLeft e).rightAdjointUniq b

/-- 右随伴の比較が満たす、二つの評価の比較の法則。 -/
def evaluationLaw (X : D) : Prop :=
  L'.map ((rightIso a b e).hom.app X) ≫ b.counit.app X =
    e.inv.app (R.obj X) ≫ a.counit.app X

/-- 右随伴の比較は、左随伴の逆比較を介して元の評価を保つ。 -/
lemma rightIso_evaluation (X : D) : evaluationLaw a b e X :=
  (a.ofNatIsoLeft e).rightAdjointUniq_hom_app_counit b X

/-- 左随伴の比較と右随伴の比較が、二つの転置を比較する法則。 -/
def homEquivLaw (X : C) (Y : D) (f : L'.obj X ⟶ Y) : Prop :=
  a.homEquiv X Y (e.hom.app X ≫ f) ≫ (rightIso a b e).hom.app Y = b.homEquiv X Y f

/-- 右随伴の比較を元の転置へ合成すると、比較後の左随伴の転置になる。 -/
lemma rightIso_homEquiv (X : C) (Y : D) (f : L'.obj X ⟶ Y) : homEquivLaw a b e X Y f := by
  change a.homEquiv X Y (e.hom.app X ≫ f) ≫ (rightIso a b e).hom.app Y = b.homEquiv X Y f
  rw [← Adjunction.homEquiv_ofNatIsoLeft_apply]
  simp only [Adjunction.homEquiv_unit, Category.assoc]
  rw [(rightIso a b e).hom.naturality f, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ R'.map f)
    ((a.ofNatIsoLeft e).unit_rightAdjointUniq_hom_app b X)

end SerrePositivity.ActionComparisonAdjunction
end

end ActionComparisonAdjunction

/-! ## ActionUnitAdjunction（旧 SerrePositivity/CategoryTheory/Monoidal/ActionUnitAdjunction.lean） -/

/-! # 作用の単位比較を随伴の右随伴へ送る -/

@[expose] public section ActionUnitAdjunction
universe v u

noncomputable section

namespace SerrePositivity.ActionUnitAdjunction

open CategoryTheory

variable {C : Type u} [Category.{v} C] {L R : C ⥤ C}
  (a : L ⊣ R) (e : L ≅ 𝟭 C)

/-- 左随伴の単位比較から得る右随伴の単位比較。 -/
def rightUnitIso : R ≅ 𝟭 C := (a.ofNatIsoLeft e).rightAdjointUniq Adjunction.id

/-- 右随伴の単位比較を元の評価で計算する。 -/
lemma rightUnitIso_hom (X : C) :
    (rightUnitIso a e).hom.app X = e.inv.app (R.obj X) ≫ a.counit.app X := by
  have h := (a.ofNatIsoLeft e).rightAdjointUniq_hom_app_counit Adjunction.id X
  change (rightUnitIso a e).hom.app X ≫ 𝟙 X =
    e.inv.app (R.obj X) ≫ a.counit.app X at h
  erw [Category.comp_id] at h
  exact h

end SerrePositivity.ActionUnitAdjunction
end

end ActionUnitAdjunction

/-! ## HomEquivNaturality（旧 SerrePositivity/CategoryTheory/Monoidal/HomEquivNaturality.lean） -/

/-! # 二つのHom同値の自然性から得る第三の同値の自然性 -/

@[expose] public section HomEquivNaturality
universe u₁ u₂ u₃ u₁' u₂' u₃'

namespace SerrePositivity.HomEquivNaturality

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  {A' : Type u₁'} {B' : Type u₂'} {C' : Type u₃'}
  (q : A ≃ B) (q' : A' ≃ B') (r : A ≃ C) (r' : A' ≃ C')
  (f : A → A') (g : B → B') (h : C → C')

/-- 共通の原変数を介して得た同値の自然性の等式。 -/
def derivedLaw (y : B) : Prop := (q'.symm.trans r') (g y) = h ((q.symm.trans r) y)

/-- 共通の原変数からの二つの同値の自然性を、残りの二つの型の同値へ送る。 -/
lemma derived (hq : ∀ x, q' (f x) = g (q x)) (hr : ∀ x, r' (f x) = h (r x))
    (y : B) : derivedLaw q q' r r' g h y := by
  have hx := hq (q.symm y)
  rw [q.apply_symm_apply] at hx
  have hi : q'.symm (g y) = f (q.symm y) := (q'.symm_apply_eq).mpr hx.symm
  unfold derivedLaw
  rw [Equiv.trans_apply, Equiv.trans_apply, hi]
  exact hr (q.symm y)

end SerrePositivity.HomEquivNaturality

end HomEquivNaturality

/-! ## AdjunctionHomLaws（旧 SerrePositivity/CategoryTheory/AdjunctionHomLaws.lean） -/

/-! # 随伴の転置・逆転置の法則の命題としての公開 -/

@[expose] public section AdjunctionHomLaws
universe v₁ v₂ u₁ u₂

namespace SerrePositivity.AdjunctionHomLaws

open CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)

/-- 転置して逆転置すると元の射になるという法則。 -/
def uncurryCurryLaw {X : C} {Y : D} (f : L.obj X ⟶ Y) : Prop :=
  (a.homEquiv X Y).symm (a.homEquiv X Y f) = f

/-- 逆転置して転置すると元の射になるという法則。 -/
def curryUncurryLaw {X : C} {Y : D} (f : X ⟶ R.obj Y) : Prop :=
  a.homEquiv X Y ((a.homEquiv X Y).symm f) = f

/-- 転置の値域の射に関する自然性の法則。 -/
def curryNaturalityRightLaw {X : C} {Y Z : D} (f : L.obj X ⟶ Y) (g : Y ⟶ Z) : Prop :=
  a.homEquiv X Z (f ≫ g) = a.homEquiv X Y f ≫ R.map g

/-- 転置のパラメータの射に関する自然性の法則。 -/
def curryNaturalityLeftLaw {X Y : C} {Z : D} (f : X ⟶ Y) (g : L.obj Y ⟶ Z) : Prop :=
  a.homEquiv X Z (L.map f ≫ g) = f ≫ a.homEquiv Y Z g

/-- 随伴の転置のパラメータに関する自然性。 -/
lemma curry_naturality_left {X Y : C} {Z : D} (f : X ⟶ Y) (g : L.obj Y ⟶ Z) :
    curryNaturalityLeftLaw a f g := a.homEquiv_naturality_left f g

/-- 随伴の転置・逆転置の左相互逆性。 -/
lemma uncurry_curry {X : C} {Y : D} (f : L.obj X ⟶ Y) : uncurryCurryLaw a f :=
  (a.homEquiv X Y).left_inv f

/-- 随伴の転置・逆転置の右相互逆性。 -/
lemma curry_uncurry {X : C} {Y : D} (f : X ⟶ R.obj Y) : curryUncurryLaw a f :=
  (a.homEquiv X Y).right_inv f

/-- 随伴の転置の値域に関する自然性。 -/
lemma curry_naturality_right {X : C} {Y Z : D} (f : L.obj X ⟶ Y) (g : Y ⟶ Z) :
    curryNaturalityRightLaw a f g := a.homEquiv_naturality_right f g

/-- 転置した射を左随伴で送って評価すると元の射になるという法則。 -/
def curryEvaluationLaw {X : C} {Y : D} (f : L.obj X ⟶ Y) : Prop :=
  L.map (a.homEquiv X Y f) ≫ a.counit.app Y = f

/-- 転置した射を評価すると元の射になる。 -/
lemma curry_evaluation {X : C} {Y : D} (f : L.obj X ⟶ Y) :
    curryEvaluationLaw a f := by
  change L.map (a.homEquiv X Y f) ≫ a.counit.app Y = f
  exact (a.homEquiv X Y).left_inv f

/-- 左随伴で送って評価した二つの射が等しいという法則。 -/
def evaluationEqualityLaw {X : C} {Y : D} (f g : X ⟶ R.obj Y) : Prop :=
  L.map f ≫ a.counit.app Y = L.map g ≫ a.counit.app Y

/-- 右随伴への射は左随伴で送った後の評価で決まる。 -/
lemma evaluation_injective {X : C} {Y : D} (f g : X ⟶ R.obj Y)
    (h : evaluationEqualityLaw a f g) : f = g :=
  (a.homEquiv X Y).symm.injective h

/-- 転置した射への前合成を、評価後の等式から特徴付ける法則。 -/
def curryPreEqualityLaw {X Z : C} {Y : D} (f : L.obj X ⟶ Y)
    (t : Z ⟶ X) (s : Z ⟶ R.obj Y) : Prop :=
  t ≫ a.homEquiv X Y f = s

/-- 前合成した転置は評価後の等式で決まる。 -/
lemma curry_pre_eq_of_evaluation {X Z : C} {Y : D} (f : L.obj X ⟶ Y)
    (t : Z ⟶ X) (s : Z ⟶ R.obj Y)
    (h : L.map t ≫ f = L.map s ≫ a.counit.app Y) : curryPreEqualityLaw a f t s := by
  apply evaluation_injective a
  change L.map (t ≫ a.homEquiv X Y f) ≫ a.counit.app Y = _
  rw [L.map_comp, Category.assoc]
  have hc := curry_evaluation a f
  change L.map (a.homEquiv X Y f) ≫ a.counit.app Y = f at hc
  rw [hc]
  exact h

/-- 二つの転置への前合成を比較する等式。 -/
def curryPreComparisonLaw {X X' Z : C} {Y : D} (f : L.obj X ⟶ Y)
    (g : L.obj X' ⟶ Y) (t : Z ⟶ X) (s : Z ⟶ X') : Prop :=
  t ≫ a.homEquiv X Y f = s ≫ a.homEquiv X' Y g

/-- 二つの転置への前合成は評価後の等式から比較できる。 -/
lemma curry_pre_comparison_of_evaluation {X X' Z : C} {Y : D} (f : L.obj X ⟶ Y)
    (g : L.obj X' ⟶ Y) (t : Z ⟶ X) (s : Z ⟶ X')
    (h : L.map t ≫ f = L.map s ≫ g) : curryPreComparisonLaw a f g t s := by
  apply evaluation_injective a
  change L.map (t ≫ a.homEquiv X Y f) ≫ a.counit.app Y =
    L.map (s ≫ a.homEquiv X' Y g) ≫ a.counit.app Y
  rw [L.map_comp, L.map_comp]
  simp only [Category.assoc]
  have hf := curry_evaluation a f
  have hg := curry_evaluation a g
  change L.map (a.homEquiv X Y f) ≫ a.counit.app Y = f at hf
  change L.map (a.homEquiv X' Y g) ≫ a.counit.app Y = g at hg
  rw [hf, hg]
  exact h

/-- 左随伴の指定した対象との比較から、元の射を右随伴への射へ転置する同値。 -/
def comparisonHomEquiv {I : C} {E : D} (e : L.obj I ≅ E) (F : D) :
    (E ⟶ F) ≃ (I ⟶ R.obj F) :=
  (Iso.homCongr e.symm (Iso.refl F)).trans (a.homEquiv I F)

/-- 比較を使うHom同値の順写像。 -/
lemma comparisonHomEquiv_apply {I : C} {E F : D} (e : L.obj I ≅ E) (f : E ⟶ F) :
    comparisonHomEquiv a e F f = a.homEquiv I F (e.hom ≫ f) := by
  simp only [comparisonHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.symm_inv, Iso.refl_hom, Category.comp_id]

/-- 比較を使うHom同値の逆写像。 -/
lemma comparisonHomEquiv_symm_apply {I : C} {E F : D} (e : L.obj I ≅ E)
    (f : I ⟶ R.obj F) :
    (comparisonHomEquiv a e F).symm f = e.inv ≫ (a.homEquiv I F).symm f := by
  change e.inv ≫ ((a.homEquiv I F).symm f ≫ 𝟙 F) = _
  rw [Category.comp_id]

/-- 恒等射を比較の順射の転置へ送るという法則。 -/
def comparisonEvaluationLaw {I : C} {E F : D} (e : L.obj I ≅ E) (f : E ⟶ F) : Prop :=
  L.map (comparisonHomEquiv a e F f) ≫ a.counit.app F = e.hom ≫ f

/-- 比較を使うHom同値で送った射を評価すると、比較と元の射の合成になる。 -/
lemma comparison_evaluation {I : C} {E F : D} (e : L.obj I ≅ E) (f : E ⟶ F) :
    comparisonEvaluationLaw a e f := by
  unfold comparisonEvaluationLaw
  rw [comparisonHomEquiv_apply]
  exact curry_evaluation a (e.hom ≫ f)

/-- 恒等射を比較の順射の転置へ送るという法則。 -/
def comparisonHomIdentityLaw {I : C} {E : D} (e : L.obj I ≅ E) : Prop :=
  comparisonHomEquiv a e E (𝟙 E) = a.homEquiv I E e.hom

/-- 恒等射は比較の順射を転置した射に対応する。 -/
lemma comparisonHomEquiv_id {I : C} {E : D} (e : L.obj I ≅ E) :
    comparisonHomIdentityLaw a e := by
  unfold comparisonHomIdentityLaw
  rw [comparisonHomEquiv_apply, Category.comp_id]

end SerrePositivity.AdjunctionHomLaws

end AdjunctionHomLaws

/-! ## PointwiseAdjunction（旧 SerrePositivity/CategoryTheory/PointwiseAdjunction.lean） -/

/-! # Pointwise parametrized adjunctions and evaluated pullback objects -/

@[expose] public section PointwiseAdjunction
universe s t v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.PointwiseAdjunction
variable (K : Type t) [Category.{s} K]
  {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃]

abbrev pointwise (F : C₁ ⥤ C₂ ⥤ C₃) : C₁ ⥤ (K ⥤ C₂) ⥤ (K ⥤ C₃) :=
  F ⋙ Functor.whiskeringRight K C₂ C₃

def adjunction {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂} (adj : F ⊣₂ G) :
    pointwise K F ⊣₂ pointwise K G where
  adj X := (adj.adj X).whiskerRight K
  unit_whiskerRight_map f := by
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext k
    simpa using congr_app (adj.unit_whiskerRight_map f) (M.obj k)

def evaluatePullbackObjObj (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂) [HasPullbacks C₂]
    {A B : C₁} (i : A ⟶ B) {X Y : K ⥤ C₃} (p : X ⟶ Y)
    (sq : (pointwise K G).PullbackObjObj i p) (k : K) :
    G.PullbackObjObj i (p.app k) where
  pt := sq.pt.obj k
  fst := sq.fst.app k
  snd := sq.snd.app k
  isPullback := sq.isPullback.map ((evaluation K C₂).obj k)
  π := sq.π.app k
  π_fst := congr_app sq.π_fst k
  π_snd := congr_app sq.π_snd k

end SerrePositivity.PointwiseAdjunction
end

end PointwiseAdjunction

/-! ## ParametrizedAdjunctionTransport（旧 SerrePositivity/CategoryTheory/ParametrizedAdjunctionTransport.lean） -/

/-! # Restriction and transport of parametrized adjunctions

Natural comparisons transport the parameter compatibility together with the
ordinary adjunctions. No new adjunction structure is introduced.
-/

@[expose] public section ParametrizedAdjunctionTransport
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite
namespace SerrePositivity.ParametrizedAdjunctionTransport
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {F F' : A ⥤ B ⥤ C} {G G' : Aᵒᵖ ⥤ C ⥤ B}

/-- Restrict the parameter along a functor. -/
def restrict (adj : F ⊣₂ G) (P : D ⥤ A) : (P ⋙ F) ⊣₂ (P.op ⋙ G) := by
  refine ParametrizedAdjunction.mk' (fun X ↦ adj.adj (P.obj X)) ?_
  intro X Y f Z W g
  exact adj.homEquiv_naturality_one (P.map f) g

/-- Compose an ordinary adjunction in the second input, retaining parameter naturality. -/
def composeSecond (adj : F ⊣₂ G) {L : D ⥤ B} {R : B ⥤ D} (h : L ⊣ R) :
    (F ⋙ (CategoryTheory.Functor.whiskeringLeft D B C).obj L) ⊣₂
      (G ⋙ (CategoryTheory.Functor.whiskeringRight C B D).obj R) := by
  refine ParametrizedAdjunction.mk' (fun X ↦ h.comp (adj.adj X)) ?_
  intro X Y f Z W g
  simp only [Adjunction.comp_homEquiv]
  change h.homEquiv _ _ (adj.homEquiv ((F.map f).app (L.obj Z) ≫ g)) =
    h.homEquiv _ _ (adj.homEquiv g) ≫ R.map ((G.map f.op).app W)
  rw [adj.homEquiv_naturality_one]
  exact h.homEquiv_naturality_right _ _

/-- Transport the left bifunctor through a natural isomorphism. -/
def left (adj : F ⊣₂ G) (e : F ≅ F') : F' ⊣₂ G := by
  refine ParametrizedAdjunction.mk' (fun X ↦ (adj.adj X).ofNatIsoLeft (e.app X)) ?_
  intro X Y f Z W g
  simp only [Adjunction.homEquiv_ofNatIsoLeft_apply]
  have hn := congrArg (fun t ↦ t.app Z) (e.hom.naturality f)
  change (F.map f).app Z ≫ (e.hom.app Y).app Z =
    (e.hom.app X).app Z ≫ (F'.map f).app Z at hn
  change (adj.adj X).homEquiv Z W
    ((e.hom.app X).app Z ≫ (F'.map f).app Z ≫ g) =
      (adj.adj Y).homEquiv Z W ((e.hom.app Y).app Z ≫ g) ≫ (G.map f.op).app W
  rw [← Category.assoc, ← hn, Category.assoc]
  exact adj.homEquiv_naturality_one f ((e.hom.app Y).app Z ≫ g)

/-- Transport the right bifunctor through a natural isomorphism. -/
def right (adj : F ⊣₂ G) (e : G ≅ G') : F ⊣₂ G' := by
  refine ParametrizedAdjunction.mk' (fun X ↦ (adj.adj X).ofNatIsoRight (e.app (op X))) ?_
  intro X Y f Z W g
  simp only [Adjunction.homEquiv_ofNatIsoRight_apply]
  change (adj.adj X).homEquiv Z W ((F.map f).app Z ≫ g) ≫
    (e.hom.app (op X)).app W =
      ((adj.adj Y).homEquiv Z W g ≫ (e.hom.app (op Y)).app W) ≫ (G'.map f.op).app W
  have h := adj.homEquiv_naturality_one f g
  change (adj.adj X).homEquiv Z W ((F.map f).app Z ≫ g) =
    (adj.adj Y).homEquiv Z W g ≫ (G.map f.op).app W at h
  rw [h, Category.assoc]
  have hn := congrArg (fun t ↦ t.app W) (e.hom.naturality f.op)
  change (G.map f.op).app W ≫ (e.hom.app (op X)).app W =
    (e.hom.app (op Y)).app W ≫ (G'.map f.op).app W at hn
  rw [hn, Category.assoc]

end SerrePositivity.ParametrizedAdjunctionTransport
end

end ParametrizedAdjunctionTransport

/-! ## ActionComparisonNaturality（旧 SerrePositivity/CategoryTheory/Monoidal/ActionComparisonNaturality.lean） -/

/-! # 随伴の比較のパラメータ自然性 -/

@[expose] public section ActionComparisonNaturality
universe v w u u'

noncomputable section

namespace SerrePositivity.ActionComparisonNaturality

open CategoryTheory

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{w} D]
  {L L' M M' : C ⥤ D} {R R' S S' : D ⥤ C}
  (a : L ⊣ R) (a' : L' ⊣ R') (b : M ⊣ S) (b' : M' ⊣ S')
  (e : L ≅ M) (e' : L' ≅ M')

/-- 二つの左随伴の比較の自然性に対応する、右随伴の比較の自然性の等式。 -/
def parameterLaw (q : ∀ Y, R'.obj Y ⟶ R.obj Y) (r : ∀ Y, S'.obj Y ⟶ S.obj Y)
    (Y : D) : Prop :=
  q Y ≫ (ActionComparisonAdjunction.rightIso a b e).hom.app Y =
    (ActionComparisonAdjunction.rightIso a' b' e').hom.app Y ≫ r Y

/-- 転置のパラメータ自然性と左随伴の比較の自然性は、右随伴の比較へ移る。 -/
lemma parameter (p : ∀ X, L.obj X ⟶ L'.obj X) (q : ∀ Y, R'.obj Y ⟶ R.obj Y)
    (t : ∀ X, M.obj X ⟶ M'.obj X) (r : ∀ Y, S'.obj Y ⟶ S.obj Y)
    (ha : ∀ X Y (f : L'.obj X ⟶ Y), a.homEquiv X Y (p X ≫ f) =
      a'.homEquiv X Y f ≫ q Y)
    (hb : ∀ X Y (f : M'.obj X ⟶ Y), b.homEquiv X Y (t X ≫ f) =
      b'.homEquiv X Y f ≫ r Y)
    (he : ∀ X, p X ≫ e'.hom.app X = e.hom.app X ≫ t X) (Y : D) :
    parameterLaw a a' b b' e e' q r Y := by
  let X := R'.obj Y
  let f : M'.obj X ⟶ Y := e'.inv.app X ≫ (a'.homEquiv X Y).symm (𝟙 X)
  have hf : a'.homEquiv X Y (e'.hom.app X ≫ f) = 𝟙 X := by
    simp only [f, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp,
      Equiv.apply_symm_apply]
  have hi := ActionComparisonAdjunction.rightIso_homEquiv a' b' e' X Y f
  change a'.homEquiv X Y (e'.hom.app X ≫ f) ≫
    (ActionComparisonAdjunction.rightIso a' b' e').hom.app Y = b'.homEquiv X Y f at hi
  rw [hf, Category.id_comp] at hi
  have hp := ha X Y (e'.hom.app X ≫ f)
  rw [hf, Category.id_comp] at hp
  change q Y ≫ (ActionComparisonAdjunction.rightIso a b e).hom.app Y = _
  rw [← hp]
  calc
    _ = a.homEquiv X Y (e.hom.app X ≫ t X ≫ f) ≫
        (ActionComparisonAdjunction.rightIso a b e).hom.app Y := by
      rw [← Category.assoc, he, Category.assoc]
    _ = b.homEquiv X Y (t X ≫ f) :=
      ActionComparisonAdjunction.rightIso_homEquiv a b e X Y (t X ≫ f)
    _ = b'.homEquiv X Y f ≫ r Y := hb X Y f
    _ = _ := by rw [← hi]

section Composite

variable {L₁ L₁' L₂ L₂' R₁ R₁' R₂ R₂' : C ⥤ C}
  (a₁ : L₁ ⊣ R₁) (a₁' : L₁' ⊣ R₁') (a₂ : L₂ ⊣ R₂) (a₂' : L₂' ⊣ R₂')
  (p₁ : L₁ ⟶ L₁') (p₂ : L₂ ⟶ L₂') (q₁ : R₁' ⟶ R₁) (q₂ : R₂' ⟶ R₂)

/-- 二段の合成随伴の転置のパラメータ自然性の等式。 -/
def compositePreLaw (X Y : C) (f : L₂'.obj (L₁'.obj X) ⟶ Y) : Prop :=
  (a₁.comp a₂).homEquiv X Y (p₂.app (L₁.obj X) ≫ L₂'.map (p₁.app X) ≫ f) =
    (a₁'.comp a₂').homEquiv X Y f ≫ R₁'.map (q₂.app Y) ≫ q₁.app (R₂.obj Y)

/-- 各転置の自然性と右随伴の前合成の自然性から、反復転置の自然性を得る。 -/
lemma composite_pre
    (h₁ : ∀ X Y (f : L₁'.obj X ⟶ Y), a₁.homEquiv X Y (p₁.app X ≫ f) =
      a₁'.homEquiv X Y f ≫ q₁.app Y)
    (h₂ : ∀ X Y (f : L₂'.obj X ⟶ Y), a₂.homEquiv X Y (p₂.app X ≫ f) =
      a₂'.homEquiv X Y f ≫ q₂.app Y)
    (X Y : C) (f : L₂'.obj (L₁'.obj X) ⟶ Y) :
    compositePreLaw a₁ a₁' a₂ a₂' p₁ p₂ q₁ q₂ X Y f := by
  unfold compositePreLaw
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change a₁.homEquiv X (R₂.obj Y)
    (a₂.homEquiv (L₁.obj X) Y (p₂.app (L₁.obj X) ≫ L₂'.map (p₁.app X) ≫ f)) = _
  rw [h₂, a₂'.homEquiv_naturality_left, a₁.homEquiv_naturality_right, h₁,
    Category.assoc, ← q₁.naturality]
  rfl

variable {A A' B B' : C ⥤ C} (c : A ⊣ B) (c' : A' ⊣ B')
  (d : A ≅ L₁ ⋙ L₂) (d' : A' ≅ L₁' ⋙ L₂')

/-- 合成随伴の転置の法則を使い、反復右随伴の比較の自然性を得る。 -/
lemma parameter_composite (p : ∀ X, A.obj X ⟶ A'.obj X)
    (q : ∀ Y, B'.obj Y ⟶ B.obj Y)
    (hc : ∀ X Y (f : A'.obj X ⟶ Y), c.homEquiv X Y (p X ≫ f) =
      c'.homEquiv X Y f ≫ q Y)
    (hcomp : ∀ X Y (f : L₂'.obj (L₁'.obj X) ⟶ Y),
      compositePreLaw a₁ a₁' a₂ a₂' p₁ p₂ q₁ q₂ X Y f)
    (hd : ∀ X, p X ≫ d'.hom.app X = d.hom.app X ≫
      p₂.app (L₁.obj X) ≫ L₂'.map (p₁.app X)) (Y : C) :
    parameterLaw c c' (a₁.comp a₂) (a₁'.comp a₂') d d' q
      (fun Y => R₁'.map (q₂.app Y) ≫ q₁.app (R₂.obj Y)) Y :=
  parameter c c' (a₁.comp a₂) (a₁'.comp a₂') d d' p q
    (fun X => p₂.app (L₁.obj X) ≫ L₂'.map (p₁.app X))
    (fun Y => R₁'.map (q₂.app Y) ≫ q₁.app (R₂.obj Y))
    hc (fun X Y f => by
      simpa only [compositePreLaw, Category.assoc] using hcomp X Y f) hd Y

end Composite

end SerrePositivity.ActionComparisonNaturality
end

end ActionComparisonNaturality

/-! ## AdjunctionCompositeNaturality（旧 SerrePositivity/CategoryTheory/Monoidal/AdjunctionCompositeNaturality.lean） -/

/-! # 随伴を合成したHom同値への自然性の移送 -/

@[expose] public section AdjunctionCompositeNaturality
universe v₁ v₂ v₃ u₁ u₂ u₃ u₄ u₅

namespace SerrePositivity.AdjunctionCompositeNaturality

open CategoryTheory

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
  {M M' : D ⥤ E} {N N' : E ⥤ D} (b : M ⊣ N) (b' : M' ⊣ N')

/-- 第二の随伴の転置の自然性を、合成随伴の転置へ移した等式。 -/
def preLaw {X : C} {Y : E} (t : M'.obj (L.obj X) ⟶ M.obj (L.obj X))
    (g : M.obj (L.obj X) ⟶ Y) (p : N.obj Y ⟶ N'.obj Y) : Prop :=
  (a.comp b').homEquiv X Y (t ≫ g) = (a.comp b).homEquiv X Y g ≫ R.map p

/-- 前段の随伴の値域の自然性を使い、第二の転置の自然性を合成随伴へ送る。 -/
lemma pre {X : C} {Y : E} (t : M'.obj (L.obj X) ⟶ M.obj (L.obj X))
    (g : M.obj (L.obj X) ⟶ Y) (p : N.obj Y ⟶ N'.obj Y)
    (h : b'.homEquiv (L.obj X) Y (t ≫ g) = b.homEquiv (L.obj X) Y g ≫ p) :
    preLaw a b b' t g p := by
  unfold preLaw
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change a.homEquiv X (N'.obj Y) (b'.homEquiv (L.obj X) Y (t ≫ g)) = _
  rw [h]
  exact a.homEquiv_naturality_right _ p

/-- 合成随伴の転置と別の同値を介して得た同値の自然性。 -/
def derivedPreLaw {X : C} {Y : E} {Z : Type u₄} {Z' : Type u₅}
    (r : (M.obj (L.obj X) ⟶ Y) ≃ Z) (r' : (M'.obj (L.obj X) ⟶ Y) ≃ Z')
    (p : N.obj Y ⟶ N'.obj Y) (h : Z → Z') (y : X ⟶ R.obj (N.obj Y)) : Prop :=
  HomEquivNaturality.derivedLaw ((a.comp b).homEquiv X Y) ((a.comp b').homEquiv X Y)
    r r' (fun k => k ≫ R.map p) h y

/-- 合成随伴の自然性と別の同値の自然性から、導いた同値の自然性を得る。 -/
lemma derived_pre {X : C} {Y : E} {Z : Type u₄} {Z' : Type u₅}
    (r : (M.obj (L.obj X) ⟶ Y) ≃ Z) (r' : (M'.obj (L.obj X) ⟶ Y) ≃ Z')
    (t : M'.obj (L.obj X) ⟶ M.obj (L.obj X)) (p : N.obj Y ⟶ N'.obj Y) (h : Z → Z')
    (hq : ∀ k, preLaw a b b' t k p) (hr : ∀ k, r' (t ≫ k) = h (r k))
    (y : X ⟶ R.obj (N.obj Y)) : derivedPreLaw a b b' r r' p h y :=
  HomEquivNaturality.derived ((a.comp b).homEquiv X Y) ((a.comp b').homEquiv X Y)
    r r' (fun k => t ≫ k) (fun k => k ≫ R.map p) h hq hr y

end SerrePositivity.AdjunctionCompositeNaturality

end AdjunctionCompositeNaturality
