module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.ConnectedComponents
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Limits

## 概要
関連する圏論の構成と補題をまとめる。各構成の詳細は以下の元モジュールの説明を参照。

## 方針
元の宣言と証明を保持し、依存順に section を分けて配置する。

## 規約
公開宣言名・名前空間・宇宙変数の意味を変更しない。元の module docstring は各節に保存する。

## 使われ方
旧モジュールの利用元は `SerrePositivity.CategoryTheory.Limits` を直接 import する。
-/

/-! ## InitialColimits（旧 SerrePositivity/CategoryTheory/Limits/InitialColimits.lean） -/

/-! # 始対象の図式の余極限

各対象が始対象である図式の余極限も始対象となる。
図式の添字圏は空でもよく、基礎圏の始対象の選択を仮定しない。
-/

@[expose] public section InitialColimits
universe v u w w'

noncomputable section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {J : Type w} [Category.{w'} J]

/-- 各対象が始対象である図式の余極限は始対象。 -/
def colimitOfInitialsIsInitial (F : J ⥤ C) [HasColimit F]
    (h : ∀ j, IsInitial (F.obj j)) : IsInitial (colimit F) := by
  let c (Y : C) : Cocone F := {
    pt := Y
    ι.app j := (h j).to Y
    ι.naturality i j f := (h i).hom_ext _ _ }
  apply IsInitial.ofUniqueHom (fun Y => colimit.desc F (c Y))
  intro Y f
  apply colimit.hom_ext
  intro j
  exact (h j).hom_ext _ _

end SerrePositivity
end

end InitialColimits

/-! ## SequentialExtension（旧 SerrePositivity/CategoryTheory/Limits/SequentialExtension.lean） -/

/-!
# 整合的な逐次延長族から余極限上の射を構成する

## 概要
整合的な逐次延長族から余極限上の射を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
前段を保持する延長を逐次的に選び、整合的な余錐を作る。
余極限の普遍射で全体へ降下させ、各段階への制限を確認する。

## 規約と注意
各段階の延長が前段を保持し、指定した余極限が存在することを仮定する。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。
[棚卸し m0011][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0011
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

@[expose] public section SequentialExtension
universe v u

/- 旧モジュールの技術注記（構成と注意を保存）
# Successively chosen extensions and their colimit

Each stage is chosen from extensions of the preceding stage, rather than
chosen independently. The resulting cocone retains every earlier choice.
This construction is independent of model structures and universe equality.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SequentialExtension

variable {C : Type u} [Category.{v} C] (F : ℕ ⥤ C) (P : C)
  (extend : ∀ n (a : F.obj n ⟶ P),
    {b : F.obj (n + 1) ⟶ P // F.map (homOfLE (Nat.le_succ n)) ≫ b = a})
  (a₀ : F.obj 0 ⟶ P)

/-- The next map extends the actual map selected at the preceding stage. -/
def stage : ∀ n, F.obj n ⟶ P
  | 0 => a₀
  | n + 1 => (extend n (stage n)).val

lemma stage_zero : stage F P extend a₀ 0 = a₀ := rfl

@[reassoc]
lemma stage_succ (n : ℕ) :
    F.map (homOfLE (Nat.le_succ n)) ≫ stage F P extend a₀ (n + 1) =
      stage F P extend a₀ n :=
  (extend n (stage F P extend a₀ n)).property

def cocone : Cocone F where
  pt := P
  ι := NatTrans.ofSequence (stage F P extend a₀) (by
    intro n
    simpa using stage_succ F P extend a₀ n)

@[reassoc]
lemma stage_map {n m : ℕ} (f : n ⟶ m) :
    F.map f ≫ stage F P extend a₀ m = stage F P extend a₀ n := by
  exact (cocone F P extend a₀).w f

/-- 整合的な逐次延長族から余極限上の射を構成する。

各段階の延長が前段を保持し、指定した余極限が存在することを仮定する。
前段を保持する延長を逐次的に選び、整合的な余錐を作る。
余極限の普遍射で全体へ降下させ、各段階への制限を確認する。
-/
def descend (c : Cocone F) (hc : IsColimit c) : c.pt ⟶ P :=
  hc.desc (cocone F P extend a₀)

@[reassoc]
lemma descend_stage (c : Cocone F) (hc : IsColimit c) (n : ℕ) :
    c.ι.app n ≫ descend F P extend a₀ c hc = stage F P extend a₀ n :=
  hc.fac (cocone F P extend a₀) n

lemma descend_zero (c : Cocone F) (hc : IsColimit c) :
    c.ι.app 0 ≫ descend F P extend a₀ c hc = a₀ :=
  descend_stage F P extend a₀ c hc 0

end SerrePositivity.SequentialExtension
end

end SequentialExtension

/-! ## ParametrizedGeneration（旧 SerrePositivity/CategoryTheory/LiftingProperties/ParametrizedGeneration.lean） -/

/-! # Extending pushout-product tests from generators

Parametrized adjunctions turn generator tests into right lifting properties.
Double orthogonality then extends the tests to both generated left classes,
without small-object or model-category hypotheses.
-/

@[expose] public section ParametrizedGeneration
universe u₁ v₁ u₂ v₂ u₃ v₃

noncomputable section
open CategoryTheory.Limits
namespace CategoryTheory.ParametrizedAdjunction
variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂}
  [HasPushouts C₃] [HasPullbacks C₂]

/-- Fixing the first arrow, tests on P extend to its generated left class. -/
lemma pushout_generated_second (adj : F ⊣₂ G)
    (P : MorphismProperty C₂) (Q : MorphismProperty C₃)
    {A B : C₁} (i : A ⟶ B)
    (h : ∀ {X Y : C₂} (j : X ⟶ Y), P j →
      ∀ sq : F.PushoutObjObj i j, Q.llp sq.ι)
    {X Y : C₂} (j : X ⟶ Y) (hj : P.rlp.llp j)
    (sq : F.PushoutObjObj i j) : Q.llp sq.ι := by
  intro U V p hp
  let pull := Functor.PullbackObjObj.ofHasPullback G i p
  have hr : P.rlp pull.π := by
    intro X' Y' j' hj'
    let push := Functor.PushoutObjObj.ofHasPushout F i j'
    exact (adj.hasLiftingProperty_iff push pull).1 (h j' hj' push p hp)
  exact (adj.hasLiftingProperty_iff sq pull).2 (hj _ hr)

variable {H : C₂ᵒᵖ ⥤ C₃ ⥤ C₁} [HasPullbacks C₁]

/-- Testing the original generators in both variables suffices for both
generated left classes. The target class must be a left lifting class. -/
lemma pushout_generated_both (adj : F ⊣₂ G) (adjFlip : F.flip ⊣₂ H)
    (P₁ : MorphismProperty C₁) (P₂ : MorphismProperty C₂) (Q : MorphismProperty C₃)
    (h : ∀ {A B : C₁} (i : A ⟶ B), P₁ i →
      ∀ {X Y : C₂} (j : X ⟶ Y), P₂ j →
      ∀ sq : F.PushoutObjObj i j, Q.llp sq.ι)
    {A B : C₁} (i : A ⟶ B) (hi : P₁.rlp.llp i)
    {X Y : C₂} (j : X ⟶ Y) (hj : P₂.rlp.llp j)
    (sq : F.PushoutObjObj i j) : Q.llp sq.ι := by
  apply adjFlip.pushout_generated_second P₁ Q j _ i hi sq.flip
  intro A' B' i' hi' sq'
  exact adj.pushout_generated_second P₂ Q i' (h i' hi') j hj sq'.flip

end CategoryTheory.ParametrizedAdjunction
end

end ParametrizedGeneration

/-! ## ThinComponents（旧 SerrePositivity/CategoryTheory/Groupoid/ThinComponents.lean） -/

/-! # Colimit morphism properties over thin groupoids

A groupoid with at most one morphism between any two objects is equivalent to
its discrete set of connected components. Thus a morphism class stable under
coproducts is stable under these colimits. This accounts for the freeness of
induction indexing categories without treating arbitrary orbit quotients as
coproducts.
-/

@[expose] public section ThinComponents
universe u v u' v'

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.ThinGroupoid
variable {J : Type u} [Category.{v} J] [IsGroupoid J]

lemma nonempty_hom_of_zigzag {X Y : J} (h : Zigzag X Y) : Nonempty (X ⟶ Y) := by
  induction h with
  | refl => exact ⟨𝟙 _⟩
  | tail _ hz ih =>
    obtain ⟨f⟩ := ih
    rcases hz with hg | hg
    · obtain ⟨g⟩ := hg
      exact ⟨f ≫ g⟩
    · obtain ⟨g⟩ := hg
      exact ⟨f ≫ inv g⟩

/-- The projection onto connected components, as a discrete category. -/
def componentProjection : J ⥤ Discrete (ConnectedComponents J) :=
  ConnectedComponents.functorToDiscrete _ id

instance [Quiver.IsThin J] : (componentProjection (J := J)).Faithful where
  map_injective := fun _ ↦ Subsingleton.elim _ _

instance : (componentProjection (J := J)).Full where
  map_surjective {X Y} f := by
    have h : Quotient.mk (Zigzag.setoid J) X = Quotient.mk (Zigzag.setoid J) Y :=
      Discrete.eq_of_hom f
    exact ⟨(nonempty_hom_of_zigzag (Quotient.exact h)).some, Subsingleton.elim _ _⟩

instance : (componentProjection (J := J)).EssSurj where
  mem_essImage q := by
    obtain ⟨X, hX⟩ := Quotient.exists_rep q.as
    exact ⟨X, ⟨eqToIso (Discrete.ext hX)⟩⟩

instance [Quiver.IsThin J] : (componentProjection (J := J)).IsEquivalence where

/-- Choice-independent at the projection level; the selected inverse is the
ordinary Mathlib inverse of a fully faithful essentially surjective functor. -/
def discreteEquivalence [Quiver.IsThin J] : J ≌ Discrete (ConnectedComponents J) :=
  (componentProjection (J := J)).asEquivalence

variable {C : Type u'} [Category.{v'} C] (P : MorphismProperty C)

lemma colimitsOfShape_le [Quiver.IsThin J]
    [P.IsStableUnderCoproductsOfShape (ConnectedComponents J)] : P.colimitsOfShape J ≤ P := by
  rw [P.colimitsOfShape_eq_of_equivalence (discreteEquivalence (J := J))]
  exact P.colimitsOfShape_le

lemma isStableUnderColimitsOfShape [Quiver.IsThin J]
    [P.IsStableUnderCoproductsOfShape (ConnectedComponents J)] :
    P.IsStableUnderColimitsOfShape J :=
  (P.isStableUnderColimitsOfShape_iff_colimitsOfShape_le J).2 (colimitsOfShape_le P)
end SerrePositivity.ThinGroupoid
end

end ThinComponents

/-! ## FiniteBijection（旧 SerrePositivity/CategoryTheory/FiniteBijection.lean） -/

/-!
# 有限集合と全単射の小さい骨格

Mathlib の有限集合の標準骨格の core を使う小さい亜群。
対象は有限の濃度、射はその標準有限集合の全単射であり、一般の写像を含めない。
射と `Fin n` の同値の対応を明示して、置換作用の規約を固定する。
対称列以外にも使える共通の圏論基盤。
-/

@[expose] public section FiniteBijection

namespace SerrePositivity

open CategoryTheory

/-- 有限集合の標準骨格における全単射の圏。 -/
abbrev FiniteBijection := Core FintypeCat.Skeleton.{0}

namespace FiniteBijection

/-- n 元の標準有限集合。 -/
def of (n : ℕ) : FiniteBijection := ⟨FintypeCat.Skeleton.mk n⟩

/-- 対象の濃度。 -/
def card (X : FiniteBijection) : ℕ := (Core.of X).len

@[simp] lemma card_of (n : ℕ) : card (of n) = n := rfl

@[simp] lemma of_card (X : FiniteBijection) : of (card X) = X := by
  cases X with | mk X => cases X; rfl

/-- 全単射を core の射へ戻す。 -/
def homOfEquiv {X Y : FiniteBijection} (e : Fin (card X) ≃ Fin (card Y)) : X ⟶ Y :=
  ⟨{ hom := fun x ↦ ⟨e x.down⟩
     inv := fun y ↦ ⟨e.symm y.down⟩
     hom_inv_id := by funext x; apply ULift.ext; exact e.symm_apply_apply x.down
     inv_hom_id := by funext y; apply ULift.ext; exact e.apply_symm_apply y.down }⟩

/-- core の射を標準有限集合の全単射として読む。 -/
def equivOfHom {X Y : FiniteBijection} (f : X ⟶ Y) : Fin (card X) ≃ Fin (card Y) where
  toFun x := (f.iso.hom ⟨x⟩).down
  invFun y := (f.iso.inv ⟨y⟩).down
  left_inv x := by
    have h := congrFun f.iso.hom_inv_id (ULift.up x)
    exact congrArg ULift.down h
  right_inv y := by
    have h := congrFun f.iso.inv_hom_id (ULift.up y)
    exact congrArg ULift.down h

/-- 射は、まさに標準有限集合の全単射。 -/
def homEquiv (X Y : FiniteBijection) : (X ⟶ Y) ≃ (Fin (card X) ≃ Fin (card Y)) where
  toFun := equivOfHom
  invFun := homOfEquiv
  left_inv f := by
    apply Core.hom_ext
    funext x
    rfl
  right_inv e := by ext x; rfl

@[simp] lemma equivOfHom_homOfEquiv {X Y : FiniteBijection}
    (e : Fin (card X) ≃ Fin (card Y)) : equivOfHom (homOfEquiv e) = e :=
  (homEquiv X Y).apply_symm_apply e

@[simp] lemma homOfEquiv_equivOfHom {X Y : FiniteBijection} (f : X ⟶ Y) :
    homOfEquiv (equivOfHom f) = f := (homEquiv X Y).symm_apply_apply f

@[simp] lemma homOfEquiv_refl (X : FiniteBijection) :
    homOfEquiv (Equiv.refl (Fin (card X))) = 𝟙 X := by
  apply Core.hom_ext
  rfl

@[simp] lemma homOfEquiv_trans {X Y Z : FiniteBijection}
    (e : Fin (card X) ≃ Fin (card Y)) (f : Fin (card Y) ≃ Fin (card Z)) :
    homOfEquiv (e.trans f) = homOfEquiv e ≫ homOfEquiv f := by
  apply Core.hom_ext
  rfl

/-- 射があると二つの濃度は等しい。 -/
lemma card_eq_of_hom {X Y : FiniteBijection} (f : X ⟶ Y) : card X = card Y :=
  Fin.equiv_iff_eq.mp ⟨equivOfHom f⟩

/-- 標準対象の自己同型は n 文字の置換。 -/
def permutation (n : ℕ) (σ : Equiv.Perm (Fin n)) : of n ⟶ of n := homOfEquiv σ

@[simp] lemma permutation_one (n : ℕ) : permutation n 1 = 𝟙 (of n) := homOfEquiv_refl _

/-- 群の積と圏の合成では順序が逆になる。作用の乗法則に使う。 -/
lemma permutation_mul (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    permutation n (σ * τ) = permutation n τ ≫ permutation n σ :=
  homOfEquiv_trans (X := of n) (Y := of n) (Z := of n) τ σ

/-- 全ての有限集合の全単射圏への標準包含。 -/
def inclusion : FiniteBijection ⥤ Core FintypeCat.{0} := FintypeCat.Skeleton.incl.core

/-- 射があると骨格の対象そのものが等しい。 -/
lemma object_eq_of_hom {X Y : FiniteBijection} (f : X ⟶ Y) : X = Y := by
  rw [← of_card X, ← of_card Y, card_eq_of_hom f]

@[simp] lemma equivOfHom_id (X : FiniteBijection) :
    equivOfHom (𝟙 X) = Equiv.refl (Fin (card X)) := by ext x; rfl

@[simp] lemma equivOfHom_comp {X Y Z : FiniteBijection} (f : X ⟶ Y) (g : Y ⟶ Z) :
    equivOfHom (f ≫ g) = (equivOfHom f).trans (equivOfHom g) := by ext x; rfl

end FiniteBijection
end SerrePositivity

end FiniteBijection

/-! ## FiniteBlockEquiv（旧 SerrePositivity/CategoryTheory/FiniteBlockEquiv.lean） -/

/-! # 標準有限集合のブロック全単射

左右の有限全単射を、連結した標準有限集合上の全単射へまとめる。
スペクトルや添字圏に依存しない、有限集合についての一般論。
-/

@[expose] public section FiniteBlockEquiv

namespace SerrePositivity.FiniteBijection

/-- 二つの全単射を、直和の二つのブロックに作用させる。 -/
def blockEquiv {m n m' n' : ℕ} (e : Fin m ≃ Fin m') (f : Fin n ≃ Fin n') :
    Fin (m + n) ≃ Fin (m' + n') :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e f).trans finSumFinEquiv)

@[simp] lemma blockEquiv_refl (m n : ℕ) :
    blockEquiv (Equiv.refl (Fin m)) (Equiv.refl (Fin n)) = Equiv.refl (Fin (m + n)) := by
  ext x
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective x
  cases i <;> simp [blockEquiv]

lemma blockEquiv_trans {m n m' n' m'' n'' : ℕ}
    (e : Fin m ≃ Fin m') (f : Fin n ≃ Fin n')
    (e' : Fin m' ≃ Fin m'') (f' : Fin n' ≃ Fin n'') :
    (blockEquiv e f).trans (blockEquiv e' f') = blockEquiv (e.trans e') (f.trans f') := by
  ext x
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective x
  cases i <;> simp [blockEquiv]

/-- 左ブロックの二点の交換は、連結後の同じ二点の交換。 -/
lemma blockEquiv_swap_left (m n : ℕ) (i j : Fin m) :
    blockEquiv (Equiv.swap i j) (Equiv.refl (Fin n)) =
      Equiv.swap (i.castAdd n) (j.castAdd n) := by
  simp only [blockEquiv, Equiv.Perm.sumCongr_swap_refl]
  simpa only [← Equiv.trans_assoc, finSumFinEquiv_apply_left] using
    Equiv.symm_trans_swap_trans (Sum.inl i) (Sum.inl j) finSumFinEquiv
/-- 右ブロックの二点の交換は、左ブロックの長さだけずらした交換。 -/
lemma blockEquiv_swap_right (m n : ℕ) (i j : Fin n) :
    blockEquiv (Equiv.refl (Fin m)) (Equiv.swap i j) =
      Equiv.swap (i.natAdd m) (j.natAdd m) := by
  simp only [blockEquiv, Equiv.Perm.sumCongr_refl_swap]
  simpa only [← Equiv.trans_assoc, finSumFinEquiv_apply_right] using
    Equiv.symm_trans_swap_trans (Sum.inr i) (Sum.inr j) finSumFinEquiv

/-- ブロック全単射は左右の置換の乗法を保つ。 -/
lemma blockEquiv_mul {m n : ℕ} (σ τ : Equiv.Perm (Fin m))
    (α β : Equiv.Perm (Fin n)) :
    blockEquiv (σ * τ) (α * β) = blockEquiv σ α * blockEquiv τ β := by
  exact (blockEquiv_trans τ β σ α).symm

end SerrePositivity.FiniteBijection

end FiniteBlockEquiv

/-! ## CommaIdentities（旧 SerrePositivity/CategoryTheory/CommaIdentities.lean） -/

/-! # Reflection of identity arrows by over and under projections

An over or under triangle whose varying side is an identity is itself an
identity. The statement uses the actual identity-arrow property, allowing
its use in strict degree inequalities without replacing identities by isos.
-/

@[expose] public section CommaIdentities
universe v u

open CategoryTheory

namespace SerrePositivity.CommaIdentities
variable {C : Type u} [Category.{v} C]

lemma under_homMk {j X Y : C} (f : j ⟶ X) (g : j ⟶ Y) (h : X ⟶ Y)
    (hh : MorphismProperty.identities C h) (w : f ≫ h = g) :
    MorphismProperty.identities (Under j)
      (Under.homMk (U := Under.mk f) (V := Under.mk g) h w) := by
  cases hh
  have hfg : f = g := by simpa only [Category.comp_id] using w
  cases hfg
  have he : Under.homMk (U := Under.mk f) (V := Under.mk f) (𝟙 X) =
      𝟙 (Under.mk f) := by ext; rfl
  exact he.symm ▸ MorphismProperty.ofHoms.mk (Under.mk f)

lemma under_reflect {j : C} {f g : Under j} (φ : f ⟶ g)
    (hφ : MorphismProperty.identities C φ.right) :
    MorphismProperty.identities (Under j) φ := by
  obtain ⟨X, f, rfl⟩ := Under.mk_surjective f
  obtain ⟨Y, g, rfl⟩ := Under.mk_surjective g
  exact under_homMk f g φ.right hφ (Under.w φ)

lemma over_homMk {j X Y : C} (f : X ⟶ j) (g : Y ⟶ j) (h : X ⟶ Y)
    (hh : MorphismProperty.identities C h) (w : h ≫ g = f) :
    MorphismProperty.identities (Over j)
      (Over.homMk (U := Over.mk f) (V := Over.mk g) h w) := by
  cases hh
  have hgf : g = f := by simpa only [Category.id_comp] using w
  cases hgf
  have he : Over.homMk (U := Over.mk f) (V := Over.mk f) (𝟙 X) =
      𝟙 (Over.mk f) := by ext; rfl
  exact he.symm ▸ MorphismProperty.ofHoms.mk (Over.mk f)

lemma over_reflect {j : C} {f g : Over j} (φ : f ⟶ g)
    (hφ : MorphismProperty.identities C φ.left) :
    MorphismProperty.identities (Over j) φ := by
  obtain ⟨X, f, rfl⟩ := Over.mk_surjective f
  obtain ⟨Y, g, rfl⟩ := Over.mk_surjective g
  exact over_homMk f g φ.left hφ (Over.w φ)

end SerrePositivity.CommaIdentities

end CommaIdentities

/-! ## RelativeArrow（旧 SerrePositivity/CategoryTheory/RelativeArrow.lean） -/

/-! # Relative pushout and pullback arrows of a natural transformation

A natural transformation A ⟶ B produces two functors on arrow categories:
the relative pushout A(y) ⨿_{A(x)} B(x) ⟶ B(y), and the relative pullback
A(x) ⟶ A(y) ×_{B(y)} B(x). The construction acts on all commutative squares,
so in particular preserves arrow isomorphisms and retract diagrams.
-/

@[expose] public section RelativeArrow
universe v u v' u'

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.RelativeArrow
variable {D : Type u} [Category.{v} D] {C : Type u'} [Category.{v'} C]
  {A B : D ⥤ C} (α : A ⟶ B)

section Pushout
variable [HasPushouts C]

abbrev pushoutArrow {x y : D} (f : x ⟶ y) :
    pushout (A.map f) (α.app x) ⟶ B.obj y :=
  pushout.desc (α.app y) (B.map f) (α.naturality f)

abbrev pushoutMap {f g : Arrow D} (s : f ⟶ g) :
    pushout (A.map f.hom) (α.app f.left) ⟶ pushout (A.map g.hom) (α.app g.left) :=
  pushout.map _ _ _ _ (A.map s.right) (B.map s.left) (A.map s.left)
    (by rw [← A.map_comp, ← A.map_comp, s.w]) (α.naturality s.left).symm

@[reassoc (attr := simp)]
lemma inl_pushoutMap {f g : Arrow D} (s : f ⟶ g) :
    pushout.inl _ _ ≫ pushoutMap α s = A.map s.right ≫ pushout.inl _ _ :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inr_pushoutMap {f g : Arrow D} (s : f ⟶ g) :
    pushout.inr _ _ ≫ pushoutMap α s = B.map s.left ≫ pushout.inr _ _ :=
  pushout.inr_desc _ _ _

lemma pushoutMap_square {f g : Arrow D} (s : f ⟶ g) :
    pushoutMap α s ≫ pushoutArrow α g.hom = pushoutArrow α f.hom ≫ B.map s.right := by
  apply pushout.hom_ext
  · rw [inl_pushoutMap_assoc, pushout.inl_desc, pushout.inl_desc_assoc]
    exact α.naturality s.right
  · rw [inr_pushoutMap_assoc, pushout.inr_desc, pushout.inr_desc_assoc]
    rw [← B.map_comp, ← B.map_comp, s.w]

lemma pushoutMap_id (f : Arrow D) : pushoutMap α (𝟙 f) = 𝟙 _ := by
  apply pushout.hom_ext
  · rw [inl_pushoutMap, Category.comp_id]
    change A.map (𝟙 f.right) ≫ pushout.inl _ _ = _
    rw [A.map_id, Category.id_comp]
  · rw [inr_pushoutMap, Category.comp_id]
    change B.map (𝟙 f.left) ≫ pushout.inr _ _ = _
    rw [B.map_id, Category.id_comp]

lemma pushoutMap_comp {f g h : Arrow D} (s : f ⟶ g) (t : g ⟶ h) :
    pushoutMap α (s ≫ t) = pushoutMap α s ≫ pushoutMap α t := by
  apply pushout.hom_ext
  · rw [inl_pushoutMap, inl_pushoutMap_assoc, inl_pushoutMap]
    change A.map (s.right ≫ t.right) ≫ pushout.inl _ _ = _
    rw [A.map_comp, Category.assoc]
  · rw [inr_pushoutMap, inr_pushoutMap_assoc, inr_pushoutMap]
    change B.map (s.left ≫ t.left) ≫ pushout.inr _ _ = _
    rw [B.map_comp, Category.assoc]

def pushoutFunctor : Arrow D ⥤ Arrow C where
  obj f := Arrow.mk (pushoutArrow α f.hom)
  map s := Arrow.homMk (pushoutMap α s) (B.map s.right) (pushoutMap_square α s)
  map_id f := by
    apply Arrow.hom_ext
    · exact pushoutMap_id α f
    · exact B.map_id f.right
  map_comp s t := by
    apply Arrow.hom_ext
    · exact pushoutMap_comp α s t
    · exact B.map_comp s.right t.right

end Pushout

section Pullback
variable [HasPullbacks C]

abbrev pullbackArrow {x y : D} (f : x ⟶ y) :
    A.obj x ⟶ pullback (α.app y) (B.map f) :=
  pullback.lift (A.map f) (α.app x) (α.naturality f)

abbrev pullbackMap {f g : Arrow D} (s : f ⟶ g) :
    pullback (α.app f.right) (B.map f.hom) ⟶ pullback (α.app g.right) (B.map g.hom) :=
  pullback.map _ _ _ _ (A.map s.right) (B.map s.left) (B.map s.right)
    (α.naturality s.right).symm (by rw [← B.map_comp, ← B.map_comp, s.w])

@[reassoc (attr := simp)]
lemma pullbackMap_fst {f g : Arrow D} (s : f ⟶ g) :
    pullbackMap α s ≫ pullback.fst _ _ = pullback.fst _ _ ≫ A.map s.right :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pullbackMap_snd {f g : Arrow D} (s : f ⟶ g) :
    pullbackMap α s ≫ pullback.snd _ _ = pullback.snd _ _ ≫ B.map s.left :=
  pullback.lift_snd _ _ _

lemma pullbackMap_square {f g : Arrow D} (s : f ⟶ g) :
    A.map s.left ≫ pullbackArrow α g.hom = pullbackArrow α f.hom ≫ pullbackMap α s := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullbackMap_fst,
      ← Category.assoc, pullback.lift_fst]
    rw [← A.map_comp, ← A.map_comp, s.w]
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullbackMap_snd,
      ← Category.assoc, pullback.lift_snd]
    exact α.naturality s.left

lemma pullbackMap_id (f : Arrow D) : pullbackMap α (𝟙 f) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [pullbackMap_fst, Category.id_comp]
    change pullback.fst _ _ ≫ A.map (𝟙 f.right) = _
    rw [A.map_id, Category.comp_id]
  · rw [pullbackMap_snd, Category.id_comp]
    change pullback.snd _ _ ≫ B.map (𝟙 f.left) = _
    rw [B.map_id, Category.comp_id]

lemma pullbackMap_comp {f g h : Arrow D} (s : f ⟶ g) (t : g ⟶ h) :
    pullbackMap α (s ≫ t) = pullbackMap α s ≫ pullbackMap α t := by
  apply pullback.hom_ext
  · rw [pullbackMap_fst, Category.assoc, pullbackMap_fst, ← Category.assoc, pullbackMap_fst]
    change pullback.fst _ _ ≫ A.map (s.right ≫ t.right) = _
    rw [A.map_comp, Category.assoc]
  · rw [pullbackMap_snd, Category.assoc, pullbackMap_snd, ← Category.assoc, pullbackMap_snd]
    change pullback.snd _ _ ≫ B.map (s.left ≫ t.left) = _
    rw [B.map_comp, Category.assoc]

def pullbackFunctor : Arrow D ⥤ Arrow C where
  obj f := Arrow.mk (pullbackArrow α f.hom)
  map s := Arrow.homMk (A.map s.left) (pullbackMap α s) (pullbackMap_square α s)
  map_id f := by
    apply Arrow.hom_ext
    · exact A.map_id f.left
    · exact pullbackMap_id α f
  map_comp s t := by
    apply Arrow.hom_ext
    · exact A.map_comp s.left t.left
    · exact pullbackMap_comp α s t

end Pullback
end SerrePositivity.RelativeArrow
end

end RelativeArrow

/-! ## FiniteBijectionAction（旧 SerrePositivity/CategoryTheory/FiniteBijectionAction.lean） -/

/-!
# 各濃度の対称群作用から全単射圏上の関手へ

対象の族と各段の対称群作用を、小さい有限全単射圏上の関手へまとめる。
等しい濃度の間の移送を明示し、骨格の対象の等式から関手性を証明する。
-/

@[expose] public section FiniteBijectionAction
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.FiniteBijection

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- 全単射を、各段の作用と濃度の移送から得る射へ送る。 -/
def familyMap (A : ℕ → C) (ρ : ∀ n, Equiv.Perm (Fin n) →* Aut (A n))
    {X Y : FiniteBijection} (f : X ⟶ Y) : A (card X) ⟶ A (card Y) :=
  (ρ (card X) ((equivOfHom f).trans (finCongr (card_eq_of_hom f).symm))).asIso.hom ≫
    eqToHom (congrArg A (card_eq_of_hom f))

/-- 恒等全単射は恒等射へ送られる。 -/
lemma familyMap_id (A : ℕ → C) (ρ : ∀ n, Equiv.Perm (Fin n) →* Aut (A n))
    (X : FiniteBijection) : familyMap A ρ (𝟙 X) = 𝟙 (A (card X)) := by
  have h := congrArg (fun a : Aut (A (card X)) ↦ a.asIso.hom) ((ρ (card X)).map_one)
  simpa only [familyMap, equivOfHom_id, finCongr_refl, Equiv.trans_refl,
    eqToHom_refl, Category.comp_id, Aut.one_asIso, Iso.refl_hom, Aut.mul_asIso,
    Iso.trans_hom, Equiv.Perm.mul_def, Equiv.Perm.one_def] using h

/-- 全単射の合成は誘導射の合成へ送られる。 -/
lemma familyMap_comp (A : ℕ → C) (ρ : ∀ n, Equiv.Perm (Fin n) →* Aut (A n))
    {X Y Z : FiniteBijection} (f : X ⟶ Y) (g : Y ⟶ Z) :
    familyMap A ρ (f ≫ g) = familyMap A ρ f ≫ familyMap A ρ g := by
  cases object_eq_of_hom f
  cases object_eq_of_hom g
  have h := congrArg (fun a : Aut (A (card X)) ↦ a.asIso.hom)
    ((ρ (card X)).map_mul (equivOfHom g) (equivOfHom f))
  simpa only [familyMap, equivOfHom_comp, finCongr_refl, Equiv.trans_refl,
    eqToHom_refl, Category.comp_id, Aut.one_asIso, Iso.refl_hom, Aut.mul_asIso,
    Iso.trans_hom, Equiv.Perm.mul_def, Equiv.Perm.one_def] using h

/-- 各段の対称群作用を備えた対象の族を、全単射圏上の関手にする。 -/
def familyFunctor (A : ℕ → C) (ρ : ∀ n, Equiv.Perm (Fin n) →* Aut (A n)) :
    FiniteBijection ⥤ C where
  obj X := A (card X)
  map f := familyMap A ρ f
  map_id X := familyMap_id A ρ X
  map_comp f g := familyMap_comp A ρ f g

/-- 標準の置換の像は元の作用そのもの。 -/
lemma familyFunctor_map_permutation (A : ℕ → C)
    (ρ : ∀ n, Equiv.Perm (Fin n) →* Aut (A n)) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (familyFunctor A ρ).map (permutation n σ) = (ρ n σ).asIso.hom := by
  simp [familyFunctor, familyMap, permutation]

end SerrePositivity.FiniteBijection
end

end FiniteBijectionAction

/-! ## FiniteBijectionSum（旧 SerrePositivity/CategoryTheory/FiniteBijectionSum.lean） -/

/-!
# 標準有限集合の直和

濃度の加法と、二つの全単射を隣接したブロックへ作用させる射を構成する。
convolution を直和に沿う左 Kan 拡張として定義するための二変数関手。
直和の結合子・単位・交換の登録は別に行う。
-/

@[expose] public section FiniteBijectionSum

namespace SerrePositivity.FiniteBijection

open CategoryTheory

/-- 二つの標準有限集合の直和。 -/
def sumObj (X Y : FiniteBijection) : FiniteBijection := of (card X + card Y)

/-- 直和上の射。 -/
def sumMap {X Y X' Y' : FiniteBijection} (f : X ⟶ X') (g : Y ⟶ Y') :
    sumObj X Y ⟶ sumObj X' Y' :=
  homOfEquiv (blockEquiv (equivOfHom f) (equivOfHom g))

@[simp] lemma sumMap_id (X Y : FiniteBijection) : sumMap (𝟙 X) (𝟙 Y) = 𝟙 (sumObj X Y) := by
  simp only [sumMap, equivOfHom_id, blockEquiv_refl]
  exact homOfEquiv_refl (sumObj X Y)

@[simp] lemma sumMap_comp {X Y X' Y' X'' Y'' : FiniteBijection}
    (f : X ⟶ X') (g : Y ⟶ Y') (f' : X' ⟶ X'') (g' : Y' ⟶ Y'') :
    sumMap f g ≫ sumMap f' g' = sumMap (f ≫ f') (g ≫ g') := by
  simp only [sumMap, equivOfHom_comp, ← blockEquiv_trans]
  exact (homOfEquiv_trans (X := sumObj X Y) (Y := sumObj X' Y')
    (Z := sumObj X'' Y'') _ _).symm

/-- 有限集合の直和の二変数関手。 -/
def sumFunctor : FiniteBijection × FiniteBijection ⥤ FiniteBijection where
  obj X := sumObj X.1 X.2
  map f := sumMap f.1 f.2
  map_id X := sumMap_id X.1 X.2
  map_comp f g := (sumMap_comp f.1 f.2 g.1 g.2).symm

end SerrePositivity.FiniteBijection

end FiniteBijectionSum

/-! ## FiniteBijectionShift（旧 SerrePositivity/CategoryTheory/FiniteBijectionShift.lean） -/

/-! # 固定した有限集合を右に加える関手 -/

@[expose] public section FiniteBijectionShift

namespace SerrePositivity.FiniteBijection

open CategoryTheory

/-- n元の標準有限集合を右ブロックとして加える関手。 -/
def addRight (n : ℕ) : FiniteBijection ⥤ FiniteBijection where
  obj a := sumObj a (of n)
  map k := sumMap k (𝟙 (of n))
  map_id a := sumMap_id a (of n)
  map_comp k l := by rw [sumMap_comp, Category.id_comp]

end SerrePositivity.FiniteBijection

end FiniteBijectionShift

/-! ## FiniteBijectionInduction（旧 SerrePositivity/CategoryTheory/FiniteBijectionInduction.lean） -/

/-! # Freeness of finite-bijection induction indices

Adding a fixed right block is faithful. Its costructured arrows over a finite
set form a thin groupoid, so colimits over these indices preserve morphism
properties stable under coproducts.
-/

@[expose] public section FiniteBijectionInduction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.FiniteBijection

instance addRight_faithful (n : ℕ) : (addRight n).Faithful where
  map_injective {A B} f g h := by
    apply (homEquiv A B).injective
    apply Equiv.ext
    intro i
    have he : blockEquiv (equivOfHom f) (Equiv.refl (Fin n)) =
        blockEquiv (equivOfHom g) (Equiv.refl (Fin n)) := by
      simpa [addRight, sumMap, sumObj, card, of, FintypeCat.Skeleton.mk,
        FintypeCat.Skeleton.len] using congrArg equivOfHom h
    have hh := congrArg (fun e ↦ e (finSumFinEquiv (Sum.inl i))) he
    have hh' := congrArg
      (fun x ↦ (finSumFinEquiv : Fin (card B) ⊕ Fin n ≃ Fin (card B + n)).symm x) hh
    change equivOfHom f i = equivOfHom g i
    simpa [blockEquiv] using hh'

/-- All induction-index morphisms are invertible; the underlying finite
bijection supplies the inverse and its commuting triangle. -/
instance induction_isGroupoid (n m : ℕ) :
    IsGroupoid (CostructuredArrow (addRight n) (of m)) where
  all_isIso {A B} f := by
    let e : A ≅ B := CostructuredArrow.isoMk (asIso f.left) (CostructuredArrow.w f)
    have he : e.hom = f := CostructuredArrow.hom_ext _ _ rfl
    rw [← he]
    infer_instance

/-- The commuting triangle determines its left bijection uniquely. -/
instance induction_isThin (n m : ℕ) :
    Quiver.IsThin (CostructuredArrow (addRight n) (of m)) := by
  intro A B
  constructor
  intro f g
  apply CostructuredArrow.hom_ext
  apply (addRight n).map_injective
  apply (cancel_mono B.hom).1
  exact (CostructuredArrow.w f).trans (CostructuredArrow.w g).symm

end SerrePositivity.FiniteBijection
end

end FiniteBijectionInduction
