module

public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import Mathlib.Logic.Small.List
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import SerrePositivity.DifferentialGraded.Functor.Basic
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproductExt
public import SerrePositivity.DifferentialGraded.Complexes.TensorCarryAssociativity
public import SerrePositivity.DifferentialGraded.Complexes.TensorRightTwoCoproductExt
public import SerrePositivity.DifferentialGraded.Tensor.Graded

/-!
# Resolution.Free.Evaluation

## 概要
14 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

universe u v w

/-! ## Words（旧 SerrePositivity/DifferentialGraded/Resolution/Free/Words.lean） -/

/-! # 複体値quiverの非空有限pathのtensor項

## 概要
内部頂点のリストで非空pathを表す。空リストは一辺、恒等pathは別の添字で扱う。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Words

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v)

/-- 合成・単位をまだ持たない複体値quiver。 -/
abbrev ComplexQuiver := D → D → Complex A

/-- 非空path x→b₁→…→bᵣ→yの内部微分を持つ全次数tensor。 -/
def wordTensor (K : ComplexQuiver A D) : List D → D → D → Complex A
  | [], x, y => K x y
  | b :: w, x, y => K x b ⊗ wordTensor K w b y

/-- 辺ごとのchain mapを有限pathのtensorに延長する。 -/
def wordMap {K L : ComplexQuiver A D} (f : ∀ x y, K x y ⟶ L x y) :
    ∀ (w : List D) (x y : D), wordTensor A D K w x y ⟶ wordTensor A D L w x y
  | [], x, y => f x y
  | b :: w, x, y => f x b ⊗ₘ wordMap f w b y

lemma wordMap_id (K : ComplexQuiver A D) (w : List D) (x y : D) :
    wordMap A D (fun x y => 𝟙 (K x y)) w x y = 𝟙 (wordTensor A D K w x y) := by
  induction w generalizing x with
  | nil => rfl
  | cons b w ih =>
    change (𝟙 (K x b)) ⊗ₘ wordMap A D (fun x y => 𝟙 (K x y)) w b y = _
    rw [ih, id_tensorHom_id]
    rfl

lemma wordMap_comp {K L M : ComplexQuiver A D}
    (f : ∀ x y, K x y ⟶ L x y) (g : ∀ x y, L x y ⟶ M x y)
    (w : List D) (x y : D) :
    wordMap A D (fun x y => f x y ≫ g x y) w x y =
      wordMap A D f w x y ≫ wordMap A D g w x y := by
  induction w generalizing x with
  | nil => rfl
  | cons b w ih =>
    change (f x b ≫ g x b) ⊗ₘ wordMap A D (fun x y => f x y ≫ g x y) w b y =
      (f x b ⊗ₘ wordMap A D f w b y) ≫ (g x b ⊗ₘ wordMap A D g w b y)
    rw [ih, tensorHom_comp_tensorHom]

/-- 有限pathのtensor項のK-flat性。次数や有界性の制約は置かない。 -/
lemma wordTensor_kFlat (K : ComplexQuiver A D) (hK : ∀ x y, complexKFlat A (K x y))
    (w : List D) (x y : D) : complexKFlat A (wordTensor A D K w x y) := by
  induction w generalizing x with
  | nil => exact hK x y
  | cons b w ih => exact complexKFlat_tensor A (hK x b) (ih b)

/-- 非空pathの連結。接続頂点yを内部頂点として加える。 -/
def concatenate (w z : List D) (y : D) : List D := w ++ y :: z

/-- 連結したpath項のtensor括弧を比較する。 -/
def wordConcatenationIso (K : ComplexQuiver A D) :
    ∀ (w z : List D) (x y t : D),
      wordTensor A D K w x y ⊗ wordTensor A D K z y t ≅
        wordTensor A D K (concatenate D w z y) x t
  | [], _, _, _, _ => Iso.refl _
  | b :: w, z, x, y, t =>
    (α_ (K x b) (wordTensor A D K w b y) (wordTensor A D K z y t)) ≪≫
      (tensorLeft (K x b)).mapIso (wordConcatenationIso K w z b y t)

end SerrePositivity.DifferentialGraded.FreeDGCategory
end

end Words

/-! ## Hom（旧 SerrePositivity/DifferentialGraded/Resolution/Free/Hom.lean） -/

/-! # 自由dg圏の候補Hom複体：恒等pathと非空pathの直和

## 概要
ここでは内部微分と辺のchain mapだけを使う。cellを付ける追加微分はまだ含めない。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Hom

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v)

/-- 恒等pathの添字は端点の等式を持つ。非空pathは内部頂点のリスト。 -/
abbrev PathIndex (x y : D) := PLift (x = y) ⊕ List D

/-- 恒等pathは単位複体、非空pathは辺のtensor。 -/
def pathTensor (K : ComplexQuiver A D) {x y : D} : PathIndex D x y → Complex A
  | .inl _ => 𝟙_ (Complex A)
  | .inr w => wordTensor A D K w x y

variable [Small.{u} D]

instance pathIndexSmall (x y : D) : Small.{u} (PathIndex D x y) := inferInstance

/-- 内部微分を持つ自由Hom候補。各次数は全有限pathの直和である。 -/
abbrev homComplex (K : ComplexQuiver A D) (x y : D) : Complex A :=
  ∐ (pathTensor A D K (x := x) (y := y))

def pathInclusion (K : ComplexQuiver A D) (x y : D) (p : PathIndex D x y) :
    pathTensor A D K p ⟶ homComplex A D K x y := Sigma.ι _ p

/-- 恒等pathからの単位候補。 -/
def unitInclusion (K : ComplexQuiver A D) (x : D) :
    𝟙_ (Complex A) ⟶ homComplex A D K x x := pathInclusion A D K x x (.inl ⟨rfl⟩)

/-- 一辺pathの包含。恒等pathとは添字を分けて保持する。 -/
def edgeInclusion (K : ComplexQuiver A D) (x y : D) :
    K x y ⟶ homComplex A D K x y := pathInclusion A D K x y (.inr [])

lemma homComplex_ext (K : ComplexQuiver A D) (x y : D) {T : Complex A}
    (f g : homComplex A D K x y ⟶ T)
    (h : ∀ p, pathInclusion A D K x y p ≫ f = pathInclusion A D K x y p ≫ g) : f = g :=
  Sigma.hom_ext f g h

omit [Small.{u} D] in
lemma pathTensor_kFlat (K : ComplexQuiver A D) (hK : ∀ x y, complexKFlat A (K x y))
    {x y : D} (p : PathIndex D x y) : complexKFlat A (pathTensor A D K p) := by
  cases p with
  | inl _ => exact complexKFlat_unit A
  | inr w => exact wordTensor_kFlat A D K hK w x y

/-- 全path直和のK-flat性は辺のK-flat性から従う。 -/
lemma homComplex_kFlat (K : ComplexQuiver A D) (hK : ∀ x y, complexKFlat A (K x y))
    (x y : D) : complexKFlat A (homComplex A D K x y) := by
  have : HasExactColimitsOfShape (Discrete (PathIndex D x y)) (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (Discrete.equivalence (equivShrink.{u} (PathIndex D x y)).symm)
  exact complexKFlat_colimit A (Discrete.functor (pathTensor A D K (x := x) (y := y)))
    (fun p => pathTensor_kFlat A D K hK p.as)

end SerrePositivity.DifferentialGraded.FreeDGCategory
end

end Hom

/-! ## Maps（旧 SerrePositivity/DifferentialGraded/Resolution/Free/Maps.lean） -/

/-! # 辺のchain mapによる全path直和の関手性

## 概要
辺のchain mapによる全path直和の関手性。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Maps

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]

/-- 恒等pathを固定し、非空pathを辺ごとのtensor写像で送る。 -/
def pathMap {K L : ComplexQuiver A D} (f : ∀ x y, K x y ⟶ L x y) {x y : D} :
    ∀ p : PathIndex D x y, pathTensor A D K p ⟶ pathTensor A D L p
  | .inl _ => 𝟙 _
  | .inr w => wordMap A D f w x y

def homMap {K L : ComplexQuiver A D} (f : ∀ x y, K x y ⟶ L x y) (x y : D) :
    homComplex A D K x y ⟶ homComplex A D L x y :=
  Sigma.desc (fun p => pathMap A D f p ≫ pathInclusion A D L x y p)

lemma pathInclusion_homMap {K L : ComplexQuiver A D} (f : ∀ x y, K x y ⟶ L x y)
    (x y : D) (p : PathIndex D x y) :
    pathInclusion A D K x y p ≫ homMap A D f x y =
      pathMap A D f p ≫ pathInclusion A D L x y p := Sigma.ι_comp_desc _ _

lemma unitInclusion_homMap {K L : ComplexQuiver A D} (f : ∀ x y, K x y ⟶ L x y)
    (x : D) : unitInclusion A D K x ≫ homMap A D f x x = unitInclusion A D L x := by
  have h := pathInclusion_homMap A D f x x (.inl ⟨rfl⟩)
  exact h.trans (Category.id_comp _)

lemma edgeInclusion_homMap {K L : ComplexQuiver A D} (f : ∀ x y, K x y ⟶ L x y)
    (x y : D) : edgeInclusion A D K x y ≫ homMap A D f x y =
      f x y ≫ edgeInclusion A D L x y :=
  pathInclusion_homMap A D f x y (.inr [])

omit [Small.{u} D] in
lemma pathMap_id (K : ComplexQuiver A D) {x y : D} (p : PathIndex D x y) :
    pathMap A D (fun x y => 𝟙 (K x y)) p = 𝟙 (pathTensor A D K p) := by
  cases p with
  | inl _ => rfl
  | inr w => exact wordMap_id A D K w x y

omit [Small.{u} D] in
lemma pathMap_comp {K L M : ComplexQuiver A D}
    (f : ∀ x y, K x y ⟶ L x y) (g : ∀ x y, L x y ⟶ M x y)
    {x y : D} (p : PathIndex D x y) :
    pathMap A D (fun x y => f x y ≫ g x y) p = pathMap A D f p ≫ pathMap A D g p := by
  cases p with
  | inl _ => exact (Category.id_comp _).symm
  | inr w => exact wordMap_comp A D f g w x y

lemma homMap_id (K : ComplexQuiver A D) (x y : D) :
    homMap A D (fun x y => 𝟙 (K x y)) x y = 𝟙 (homComplex A D K x y) := by
  apply homComplex_ext A D K x y
  intro p
  rw [pathInclusion_homMap, pathMap_id, Category.id_comp, Category.comp_id]

lemma homMap_comp {K L M : ComplexQuiver A D}
    (f : ∀ x y, K x y ⟶ L x y) (g : ∀ x y, L x y ⟶ M x y) (x y : D) :
    homMap A D (fun x y => f x y ≫ g x y) x y = homMap A D f x y ≫ homMap A D g x y := by
  apply homComplex_ext A D K x y
  intro p
  rw [pathInclusion_homMap, pathMap_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (pathInclusion_homMap A D f x y p), pathInclusion_homMap]

end SerrePositivity.DifferentialGraded.FreeDGCategory
end

end Maps

/-! ## Composition（旧 SerrePositivity/DifferentialGraded/Resolution/Free/Composition.lean） -/

/-! # 自由path Homの連結chain mapと左単位

## 概要
結合則と右単位は後続で検証し、まだEnrichedCategory instanceは宣言しない。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Composition

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]

def pathComposition (K : ComplexQuiver A D) {x y z : D}
    (p : PathIndex D x y) (q : PathIndex D y z) :
    pathTensor A D K p ⊗ pathTensor A D K q ⟶ homComplex A D K x z := by
  cases p with
  | inl h =>
    rcases h with ⟨h⟩
    subst y
    exact (λ_ (pathTensor A D K q)).hom ≫ pathInclusion A D K x z q
  | inr w =>
    cases q with
    | inl h =>
      rcases h with ⟨h⟩
      subst z
      exact (ρ_ (wordTensor A D K w x y)).hom ≫ pathInclusion A D K x y (.inr w)
    | inr t =>
      exact (wordConcatenationIso A D K w t x y z).hom ≫
        pathInclusion A D K x z (.inr (concatenate D w t y))

/-- 二つの全path直和を連結する、内部微分に関するchain map。 -/
def composition (K : ComplexQuiver A D) (x y z : D) :
    homComplex A D K x y ⊗ homComplex A D K y z ⟶ homComplex A D K x z :=
  tensorCoproductDesc (pathTensor A D K (x := x) (y := y))
    (pathTensor A D K (x := y) (y := z)) (homComplex A D K x z)
    (pathComposition A D K)

lemma composition_pathInclusion (K : ComplexQuiver A D) (x y z : D)
    (p : PathIndex D x y) (q : PathIndex D y z) :
    (pathInclusion A D K x y p ⊗ₘ pathInclusion A D K y z q) ≫ composition A D K x y z =
      pathComposition A D K p q := tensorCoproductDesc_ι _ _ _ _ p q

lemma composition_nonempty (K : ComplexQuiver A D) (x y z : D) (w t : List D) :
    (pathInclusion A D K x y (.inr w) ⊗ₘ pathInclusion A D K y z (.inr t)) ≫
        composition A D K x y z =
      (wordConcatenationIso A D K w t x y z).hom ≫
        pathInclusion A D K x z (.inr (concatenate D w t y)) :=
  composition_pathInclusion A D K x y z (.inr w) (.inr t)

lemma composition_unit_path (K : ComplexQuiver A D) (x y : D) (p : PathIndex D x y) :
    (unitInclusion A D K x ⊗ₘ pathInclusion A D K x y p) ≫ composition A D K x x y =
      (λ_ (pathTensor A D K p)).hom ≫ pathInclusion A D K x y p :=
  composition_pathInclusion A D K x x y (.inl ⟨rfl⟩) p

lemma composition_left_unit (K : ComplexQuiver A D) (x y : D) :
    (unitInclusion A D K x ▷ homComplex A D K x y) ≫ composition A D K x x y =
      (λ_ (homComplex A D K x y)).hom := by
  apply (tensorLeftCoproductIsColimit (𝟙_ (Complex A))
    (pathTensor A D K (x := x) (y := y))).hom_ext
  rintro ⟨p⟩
  change (𝟙_ (Complex A) ◁ pathInclusion A D K x y p) ≫
      ((unitInclusion A D K x ▷ homComplex A D K x y) ≫ composition A D K x x y) = _
  rw [← Category.assoc, ← tensorHom_def', composition_unit_path]
  exact (leftUnitor_naturality (pathInclusion A D K x y p)).symm

end SerrePositivity.DifferentialGraded.FreeDGCategory
end

end Composition

/-! ## Units（旧 SerrePositivity/DifferentialGraded/Resolution/Free/Units.lean） -/

/-! # 自由path連結の右単位と単位pathの比較

## 概要
自由path連結の右単位と単位pathの比較。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Units

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]

lemma pathComposition_right_unit (K : ComplexQuiver A D) {x y : D} (p : PathIndex D x y) :
    pathComposition A D K p (.inl ⟨rfl⟩) =
      (ρ_ (pathTensor A D K p)).hom ≫ pathInclusion A D K x y p := by
  cases p with
  | inl h =>
    rcases h with ⟨h⟩
    subst y
    change (λ_ (𝟙_ (Complex A))).hom ≫ _ = (ρ_ (𝟙_ (Complex A))).hom ≫ _
    rw [unitors_equal]
  | inr w => rfl

lemma composition_path_unit (K : ComplexQuiver A D) (x y : D) (p : PathIndex D x y) :
    (pathInclusion A D K x y p ⊗ₘ unitInclusion A D K y) ≫ composition A D K x y y =
      (ρ_ (pathTensor A D K p)).hom ≫ pathInclusion A D K x y p :=
  (composition_pathInclusion A D K x y y p (.inl ⟨rfl⟩)).trans
    (pathComposition_right_unit A D K p)

lemma composition_right_unit (K : ComplexQuiver A D) (x y : D) :
    (homComplex A D K x y ◁ unitInclusion A D K y) ≫ composition A D K x y y =
      (ρ_ (homComplex A D K x y)).hom := by
  apply (tensorRightCoproductIsColimit (𝟙_ (Complex A))
    (pathTensor A D K (x := x) (y := y))).hom_ext
  rintro ⟨p⟩
  change (pathInclusion A D K x y p ▷ 𝟙_ (Complex A)) ≫
      ((homComplex A D K x y ◁ unitInclusion A D K y) ≫ composition A D K x y y) = _
  rw [← Category.assoc, ← tensorHom_def, composition_path_unit]
  exact (rightUnitor_naturality (pathInclusion A D K x y p)).symm

end SerrePositivity.DifferentialGraded.FreeDGCategory
end

end Units

/-! ## Evaluation（旧 SerrePositivity/DifferentialGraded/Resolution/Free/Evaluation.lean） -/

/-! # 辺のchain mapから任意のdg圏へのpath評価

## 概要
合成保存を検証する前のHom chain mapを構成する。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Evaluation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) [DGCategory A E]

/-- 非空pathを豊穣順の合成で評価する。辺の次数に制約を置かない。 -/
def wordEvaluation (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) :
    ∀ (p : List D) (x y : D), wordTensor A D K p x y ⟶ (o x ⟶[Complex A] o y)
  | [], x, y => f x y
  | b :: p, x, y => (f x b ⊗ₘ wordEvaluation K o f p b y) ≫ eComp (Complex A) (o x) (o b) (o y)

/-- 恒等pathはdg単位へ、非空pathはwordEvaluationへ送る。 -/
def pathEvaluation (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) {x y : D} :
    ∀ p : PathIndex D x y, pathTensor A D K p ⟶ (o x ⟶[Complex A] o y)
  | .inl h => by
    rcases h with ⟨h⟩
    subst y
    exact eId (Complex A) (o x)
  | .inr p => wordEvaluation A D E K o f p x y

variable [Small.{u} D]

/-- 全有限pathの直和を、指定したdg圏のHomへ評価するchain map。 -/
def homEvaluation (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) (x y : D) :
    homComplex A D K x y ⟶ (o x ⟶[Complex A] o y) :=
  Sigma.desc (pathEvaluation A D E K o f)

lemma pathInclusion_homEvaluation (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) (x y : D) (p : PathIndex D x y) :
    pathInclusion A D K x y p ≫ homEvaluation A D E K o f x y =
      pathEvaluation A D E K o f p := Sigma.ι_comp_desc _ _

lemma unitInclusion_homEvaluation (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) (x : D) :
    unitInclusion A D K x ≫ homEvaluation A D E K o f x x = eId (Complex A) (o x) :=
  pathInclusion_homEvaluation A D E K o f x x (.inl ⟨rfl⟩)

lemma edgeInclusion_homEvaluation (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) (x y : D) :
    edgeInclusion A D K x y ≫ homEvaluation A D E K o f x y = f x y :=
  pathInclusion_homEvaluation A D E K o f x y (.inr [])

end SerrePositivity.DifferentialGraded.FreeDGCategory
end

end Evaluation

/-! ## EvaluationComposition（旧 SerrePositivity/DifferentialGraded/Resolution/Free/EvaluationComposition.lean） -/

/-! # path評価と連結の整合性

## 概要
path評価と連結の整合性。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section EvaluationComposition

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) [DGCategory A E]

omit D in
lemma evaluation_tensor_assoc {K L M : Complex A} {a b c d : E}
    (f : K ⟶ (a ⟶[Complex A] b)) (g : L ⟶ (b ⟶[Complex A] c))
    (h : M ⟶ (c ⟶[Complex A] d)) :
    (α_ K L M).hom ≫ (f ⊗ₘ ((g ⊗ₘ h) ≫ eComp (Complex A) b c d)) ≫
        eComp (Complex A) a b d =
      (((f ⊗ₘ g) ≫ eComp (Complex A) a b c) ⊗ₘ h) ≫ eComp (Complex A) a c d := by
  have h₁ : (f ⊗ₘ (g ⊗ₘ h)) ≫ (𝟙 (a ⟶[Complex A] b) ⊗ₘ eComp (Complex A) b c d) =
      f ⊗ₘ ((g ⊗ₘ h) ≫ eComp (Complex A) b c d) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  rw [← h₁]
  simp only [Category.assoc]
  rw [← reassoc_of% (associator_naturality f g h), id_tensorHom, e_assoc']
  rw [← tensorHom_id, ← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]

lemma wordEvaluation_concatenation (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y))
    (p q : List D) (x y z : D) :
    (wordConcatenationIso A D K p q x y z).hom ≫
        wordEvaluation A D E K o f (concatenate D p q y) x z =
      (wordEvaluation A D E K o f p x y ⊗ₘ wordEvaluation A D E K o f q y z) ≫
        eComp (Complex A) (o x) (o y) (o z) := by
  induction p generalizing x with
  | nil => exact Category.id_comp _
  | cons b p ih =>
    change ((α_ (K x b) (wordTensor A D K p b y) (wordTensor A D K q y z)).hom ≫
        K x b ◁ (wordConcatenationIso A D K p q b y z).hom) ≫
        ((f x b ⊗ₘ wordEvaluation A D E K o f (concatenate D p q y) b z) ≫
          eComp (Complex A) (o x) (o b) (o z)) =
      (((f x b ⊗ₘ wordEvaluation A D E K o f p b y) ≫
        eComp (Complex A) (o x) (o b) (o y)) ⊗ₘ wordEvaluation A D E K o f q y z) ≫
          eComp (Complex A) (o x) (o y) (o z)
    have ht : (K x b ◁ (wordConcatenationIso A D K p q b y z).hom) ≫
        (f x b ⊗ₘ wordEvaluation A D E K o f (concatenate D p q y) b z) =
      f x b ⊗ₘ ((wordConcatenationIso A D K p q b y z).hom ≫
        wordEvaluation A D E K o f (concatenate D p q y) b z) := by
      rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
    rw [Category.assoc, ← Category.assoc _ _ (eComp (Complex A) (o x) (o b) (o z)), ht, ih]
    exact evaluation_tensor_assoc A E _ _ _

variable [Small.{u} D]

lemma pathEvaluation_composition (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) {x y z : D}
    (p : PathIndex D x y) (q : PathIndex D y z) :
    pathComposition A D K p q ≫ homEvaluation A D E K o f x z =
      (pathEvaluation A D E K o f p ⊗ₘ pathEvaluation A D E K o f q) ≫
        eComp (Complex A) (o x) (o y) (o z) := by
  cases p with
  | inl h =>
    rcases h with ⟨h⟩
    subst y
    change ((λ_ (pathTensor A D K q)).hom ≫ pathInclusion A D K x z q) ≫ _ = _
    rw [Category.assoc, pathInclusion_homEvaluation]
    have hu : (eId (Complex A) (o x) ▷ (o x ⟶[Complex A] o z)) ≫
        eComp (Complex A) (o x) (o x) (o z) = (λ_ (o x ⟶[Complex A] o z)).hom := by
      have h := congrArg (fun k => (λ_ (o x ⟶[Complex A] o z)).hom ≫ k)
        (e_id_comp (Complex A) (o x) (o z))
      simpa only [Iso.hom_inv_id_assoc, Category.comp_id] using h
    change _ = (eId (Complex A) (o x) ⊗ₘ pathEvaluation A D E K o f q) ≫ _
    rw [tensorHom_def, Category.assoc, ← whisker_exchange_assoc, hu]
    exact (leftUnitor_naturality _).symm
  | inr p =>
    cases q with
    | inl h =>
      rcases h with ⟨h⟩
      subst z
      change ((ρ_ (wordTensor A D K p x y)).hom ≫ pathInclusion A D K x y (.inr p)) ≫ _ = _
      rw [Category.assoc, pathInclusion_homEvaluation]
      change _ = (wordEvaluation A D E K o f p x y ⊗ₘ eId (Complex A) (o y)) ≫ _
      have hu : ((o x ⟶[Complex A] o y) ◁ eId (Complex A) (o y)) ≫
          eComp (Complex A) (o x) (o y) (o y) = (ρ_ (o x ⟶[Complex A] o y)).hom := by
        have h := congrArg (fun k => (ρ_ (o x ⟶[Complex A] o y)).hom ≫ k)
          (e_comp_id (Complex A) (o x) (o y))
        simpa only [Iso.hom_inv_id_assoc, Category.comp_id] using h
      rw [tensorHom_def, Category.assoc, hu]
      exact (rightUnitor_naturality _).symm
    | inr q =>
      change ((wordConcatenationIso A D K p q x y z).hom ≫
          pathInclusion A D K x z (.inr (concatenate D p q y))) ≫ _ = _
      rw [Category.assoc, pathInclusion_homEvaluation]
      exact wordEvaluation_concatenation A D E K o f p q x y z

lemma homEvaluation_composition (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) (x y z : D) :
    composition A D K x y z ≫ homEvaluation A D E K o f x z =
      (homEvaluation A D E K o f x y ⊗ₘ homEvaluation A D E K o f y z) ≫
        eComp (Complex A) (o x) (o y) (o z) := by
  apply tensorCoproduct_hom_ext (pathTensor A D K (x := x) (y := y))
    (pathTensor A D K (x := y) (y := z))
  intro p q
  change (pathInclusion A D K x y p ⊗ₘ pathInclusion A D K y z q) ≫
      (composition A D K x y z ≫ homEvaluation A D E K o f x z) =
    (pathInclusion A D K x y p ⊗ₘ pathInclusion A D K y z q) ≫
      ((homEvaluation A D E K o f x y ⊗ₘ homEvaluation A D E K o f y z) ≫
        eComp (Complex A) (o x) (o y) (o z))
  rw [← Category.assoc, composition_pathInclusion, pathEvaluation_composition,
    ← Category.assoc, tensorHom_comp_tensorHom, pathInclusion_homEvaluation,
    pathInclusion_homEvaluation]

end SerrePositivity.DifferentialGraded.FreeDGCategory
end

end EvaluationComposition

/-! ## AppendRight（旧 SerrePositivity/DifferentialGraded/Resolution/Free/AppendRight.lean） -/

/-! # 左のpathを固定した全path直和への連結

## 概要
左のpathを固定した全path直和への連結。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AppendRight

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]

def appendPath (K : ComplexQuiver A D) {x y : D} (p : PathIndex D x y) (z : D) :
    pathTensor A D K p ⊗ homComplex A D K y z ⟶ homComplex A D K x z :=
  tensorCoproductRightDesc (pathTensor A D K p) (pathTensor A D K (x := y) (y := z))
    (homComplex A D K x z) (pathComposition A D K p)

lemma appendPath_inclusion (K : ComplexQuiver A D) {x y : D}
    (p : PathIndex D x y) (z : D) (q : PathIndex D y z) :
    (pathTensor A D K p ◁ pathInclusion A D K y z q) ≫ appendPath A D K p z =
      pathComposition A D K p q := tensorCoproductRightDesc_ι _ _ _ _ q

lemma composition_left_inclusion (K : ComplexQuiver A D) (x y z : D) (p : PathIndex D x y) :
    (pathInclusion A D K x y p ▷ homComplex A D K y z) ≫ composition A D K x y z =
      appendPath A D K p z := tensorCoproductDesc_left _ _ _ _ p

/-- 固定した非空左pathと全右pathの連結。 -/
abbrev appendWord (K : ComplexQuiver A D) (w : List D) (x y z : D) :
    wordTensor A D K w x y ⊗ homComplex A D K y z ⟶ homComplex A D K x z :=
  appendPath A D K (x := x) (y := y) (.inr w) z

/-- 一辺を全右pathの先頭へ加えるchain map。 -/
abbrev edgePrefix (K : ComplexQuiver A D) (x y z : D) :
    K x y ⊗ homComplex A D K y z ⟶ homComplex A D K x z := appendWord A D K [] x y z

lemma edgePrefix_unit (K : ComplexQuiver A D) (x y : D) :
    (K x y ◁ unitInclusion A D K y) ≫ edgePrefix A D K x y y =
      (ρ_ (K x y)).hom ≫ edgeInclusion A D K x y :=
  appendPath_inclusion A D K (.inr []) y (.inl ⟨rfl⟩)

lemma edgePrefix_nonempty (K : ComplexQuiver A D) (x y z : D) (w : List D) :
    (K x y ◁ pathInclusion A D K y z (.inr w)) ≫ edgePrefix A D K x y z =
      pathInclusion A D K x z (.inr (y :: w)) := by
  have h := appendPath_inclusion A D K (x := x) (y := y) (.inr []) z (.inr w)
  exact h.trans (Category.id_comp _)

lemma appendPath_unit (K : ComplexQuiver A D) (x y : D) :
    appendPath A D K (x := x) (.inl ⟨rfl⟩) y = (λ_ (homComplex A D K x y)).hom := by
  apply (tensorLeftCoproductIsColimit (𝟙_ (Complex A))
    (pathTensor A D K (x := x) (y := y))).hom_ext
  rintro ⟨p⟩
  change (𝟙_ (Complex A) ◁ pathInclusion A D K x y p) ≫ _ = _
  exact (appendPath_inclusion A D K (x := x) (y := x) (.inl ⟨rfl⟩) y p).trans
    (leftUnitor_naturality (pathInclusion A D K x y p)).symm

end SerrePositivity.DifferentialGraded.FreeDGCategory
end

end AppendRight

/-! ## AppendRecursion（旧 SerrePositivity/DifferentialGraded/Resolution/Free/AppendRecursion.lean） -/

/-! # 非空左pathの連結を先頭一辺と短いpathへ分解する

## 概要
非空左pathの連結を先頭一辺と短いpathへ分解する。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AppendRecursion

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]

lemma appendWord_cons (K : ComplexQuiver A D) (b : D) (w : List D) (x y z : D) :
    appendWord A D K (b :: w) x y z =
      (α_ (K x b) (wordTensor A D K w b y) (homComplex A D K y z)).hom ≫
        K x b ◁ appendWord A D K w b y z ≫ edgePrefix A D K x b z := by
  apply (tensorLeftCoproductIsColimit (wordTensor A D K (b :: w) x y)
    (pathTensor A D K (x := y) (y := z))).hom_ext
  rintro ⟨q⟩
  have hl := appendPath_inclusion A D K (x := x) (y := y) (.inr (b :: w)) z q
  have hr := appendPath_inclusion A D K (x := b) (y := y) (.inr w) z q
  refine hl.trans ?_
  change pathComposition A D K (.inr (b :: w)) q =
    (((K x b ⊗ wordTensor A D K w b y) ◁ pathInclusion A D K y z q) ≫
      (α_ (K x b) (wordTensor A D K w b y) (homComplex A D K y z)).hom ≫
        K x b ◁ appendWord A D K w b y z ≫ edgePrefix A D K x b z)
  change (wordTensor A D K w b y ◁ pathInclusion A D K y z q) ≫
    appendWord A D K w b y z = pathComposition A D K (.inr w) q at hr
  rw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, hr]
  cases q with
  | inl h =>
    rcases h with ⟨h⟩
    subst z
    change (ρ_ (K x b ⊗ wordTensor A D K w b y)).hom ≫
        pathInclusion A D K x y (.inr (b :: w)) =
      (α_ (K x b) (wordTensor A D K w b y) (𝟙_ (Complex A))).hom ≫
        K x b ◁ ((ρ_ (wordTensor A D K w b y)).hom ≫
          pathInclusion A D K b y (.inr w)) ≫ edgePrefix A D K x b y
    rw [whiskerLeft_comp, Category.assoc, edgePrefix_nonempty, rightUnitor_tensor_hom,
      Category.assoc]
  | inr v =>
    change (wordConcatenationIso A D K (b :: w) v x y z).hom ≫
        pathInclusion A D K x z (.inr (b :: concatenate D w v y)) =
      (α_ (K x b) (wordTensor A D K w b y) (wordTensor A D K v y z)).hom ≫
        K x b ◁ ((wordConcatenationIso A D K w v b y z).hom ≫
          pathInclusion A D K b z (.inr (concatenate D w v y))) ≫ edgePrefix A D K x b z
    rw [whiskerLeft_comp, Category.assoc, edgePrefix_nonempty]
    rfl

end SerrePositivity.DifferentialGraded.FreeDGCategory
end

end AppendRecursion

/-! ## PrefixAssociativity（旧 SerrePositivity/DifferentialGraded/Resolution/Free/PrefixAssociativity.lean） -/

/-! # 一辺の先頭作用と任意path連結の整合性

## 概要
一辺の先頭作用と任意path連結の整合性。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PrefixAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]

lemma appendPath_edgePrefix (K : ComplexQuiver A D) (x b y z : D)
    (p : PathIndex D b y) :
    (((K x b ◁ pathInclusion A D K b y p) ≫ edgePrefix A D K x b y) ▷
        homComplex A D K y z) ≫ composition A D K x y z =
      (α_ (K x b) (pathTensor A D K p) (homComplex A D K y z)).hom ≫
        K x b ◁ appendPath A D K p z ≫ edgePrefix A D K x b z := by
  cases p with
  | inl h =>
    rcases h with ⟨h⟩
    subst y
    change (((K x b ◁ unitInclusion A D K b) ≫ edgePrefix A D K x b b) ▷
        homComplex A D K b z) ≫ composition A D K x b z = _
    have hc := composition_left_inclusion A D K x b z (.inr [])
    change (edgeInclusion A D K x b ▷ homComplex A D K b z) ≫ composition A D K x b z =
      edgePrefix A D K x b z at hc
    rw [edgePrefix_unit, comp_whiskerRight, Category.assoc, hc, appendPath_unit]
    exact congrArg (fun k => k ≫ edgePrefix A D K x b z)
      (MonoidalCategory.triangle (K x b) (homComplex A D K b z)).symm
  | inr w =>
    rw [edgePrefix_nonempty, composition_left_inclusion]
    exact appendWord_cons A D K b w x y z

lemma composition_edgePrefix (K : ComplexQuiver A D) (x b y z : D) :
    (edgePrefix A D K x b y ▷ homComplex A D K y z) ≫ composition A D K x y z =
      (α_ (K x b) (homComplex A D K b y) (homComplex A D K y z)).hom ≫
        K x b ◁ composition A D K b y z ≫ edgePrefix A D K x b z := by
  apply tensorLeftRightCoproduct_hom_ext (K x b) (homComplex A D K y z)
    (pathTensor A D K (x := b) (y := y))
  intro p
  change (((K x b ◁ pathInclusion A D K b y p) ▷ homComplex A D K y z) ≫
      (edgePrefix A D K x b y ▷ homComplex A D K y z)) ≫ composition A D K x y z = _
  rw [← comp_whiskerRight, appendPath_edgePrefix]
  symm
  have hc := composition_left_inclusion A D K b y z p
  change (Sigma.ι (pathTensor A D K (x := b) (y := y)) p ▷ homComplex A D K y z) ≫
    composition A D K b y z = appendPath A D K p z at hc
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc, hc]

end SerrePositivity.DifferentialGraded.FreeDGCategory
end

end PrefixAssociativity

/-! ## Associativity（旧 SerrePositivity/DifferentialGraded/Resolution/Free/Associativity.lean） -/

/-! # 自由path直和の連結の結合則

## 概要
自由path直和の連結の結合則。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Associativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]

lemma appendWord_assoc (K : ComplexQuiver A D) (w : List D) (x y z t : D) :
    (appendWord A D K w x y z ▷ homComplex A D K z t) ≫ composition A D K x z t =
      (α_ (wordTensor A D K w x y) (homComplex A D K y z) (homComplex A D K z t)).hom ≫
        wordTensor A D K w x y ◁ composition A D K y z t ≫ appendWord A D K w x y t := by
  induction w generalizing x with
  | nil => exact composition_edgePrefix A D K x y z t
  | cons b w ih =>
    have hk := tensorCarry_assoc (K x b) (wordTensor A D K w b y)
      (homComplex A D K y z) (homComplex A D K z t) (homComplex A D K b z)
      (homComplex A D K b t) (homComplex A D K y t)
      (appendWord A D K w b y z) (composition A D K b z t)
      (composition A D K y z t) (appendWord A D K w b y t) (ih b)
    have hp := congrArg (fun k => k ≫ edgePrefix A D K x b t) hk
    rw [appendWord_cons]
    simp only [comp_whiskerRight, Category.assoc]
    rw [composition_edgePrefix]
    simpa only [appendWord_cons, wordTensor, whiskerLeft_comp, comp_whiskerRight,
      Category.assoc] using hp

lemma appendPath_assoc (K : ComplexQuiver A D) {x y : D} (p : PathIndex D x y) (z t : D) :
    (appendPath A D K p z ▷ homComplex A D K z t) ≫ composition A D K x z t =
      (α_ (pathTensor A D K p) (homComplex A D K y z) (homComplex A D K z t)).hom ≫
        pathTensor A D K p ◁ composition A D K y z t ≫ appendPath A D K p t := by
  cases p with
  | inl h =>
    rcases h with ⟨h⟩
    subst y
    rw [appendPath_unit, appendPath_unit]
    change ((λ_ (homComplex A D K x z)).hom ▷ homComplex A D K z t) ≫
        composition A D K x z t =
      (α_ (𝟙_ (Complex A)) (homComplex A D K x z) (homComplex A D K z t)).hom ≫
        𝟙_ (Complex A) ◁ composition A D K x z t ≫ (λ_ (homComplex A D K x t)).hom
    rw [leftUnitor_naturality, ← Category.assoc, leftUnitor_tensor_hom'', tensorHom_id]
  | inr w => exact appendWord_assoc A D K w x y z t

lemma composition_assoc (K : ComplexQuiver A D) (x y z t : D) :
    (composition A D K x y z ▷ homComplex A D K z t) ≫ composition A D K x z t =
      (α_ (homComplex A D K x y) (homComplex A D K y z) (homComplex A D K z t)).hom ≫
        homComplex A D K x y ◁ composition A D K y z t ≫ composition A D K x y t := by
  apply tensorRightTwoCoproduct_hom_ext (pathTensor A D K (x := x) (y := y))
    (homComplex A D K y z) (homComplex A D K z t) (homComplex A D K x t)
  intro p
  change ((pathInclusion A D K x y p ▷ homComplex A D K y z) ▷ homComplex A D K z t) ≫
      (composition A D K x y z ▷ homComplex A D K z t) ≫ composition A D K x z t = _
  rw [← comp_whiskerRight_assoc, composition_left_inclusion,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]
  change (appendPath A D K p z ▷ homComplex A D K z t) ≫ composition A D K x z t =
    (α_ (pathTensor A D K p) (homComplex A D K y z) (homComplex A D K z t)).hom ≫
      pathTensor A D K p ◁ composition A D K y z t ≫
        (pathInclusion A D K x y p ▷ homComplex A D K y t) ≫ composition A D K x y t
  rw [composition_left_inclusion]
  exact appendPath_assoc A D K p z t

end SerrePositivity.DifferentialGraded.FreeDGCategory
end

end Associativity

/-! ## Category（旧 SerrePositivity/DifferentialGraded/Resolution/Free/Category.lean） -/

/-! # 複体値quiver上の主豊穣モデルによる自由dg圏

## 概要
複体値quiver上の主豊穣モデルによる自由dg圏。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Category

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]

/-- quiverと結び付けた自由dg圏の対象型。元のDのinstanceは変更しない。 -/
def Objects (_K : ComplexQuiver A D) : Type v := D

instance objectsSmall (K : ComplexQuiver A D) : Small.{u} (Objects A D K) :=
  inferInstanceAs (Small.{u} D)

instance dgCategory (K : ComplexQuiver A D) : DGCategory A (Objects A D K) where
  Hom X Y := homComplex A D K X Y
  id X := unitInclusion A D K X
  comp X Y Z := composition A D K X Y Z
  id_comp X Y := by
    change (λ_ (homComplex A D K X Y)).inv ≫
      (unitInclusion A D K X ▷ homComplex A D K X Y) ≫ composition A D K X X Y = _
    rw [composition_left_unit, Iso.inv_hom_id]
  comp_id X Y := by
    change (ρ_ (homComplex A D K X Y)).inv ≫
      (homComplex A D K X Y ◁ unitInclusion A D K Y) ≫ composition A D K X Y Y = _
    rw [composition_right_unit, Iso.inv_hom_id]
  assoc X Y Z T := by
    change (α_ (homComplex A D K X Y) (homComplex A D K Y Z) (homComplex A D K Z T)).inv ≫
      (composition A D K X Y Z ▷ homComplex A D K Z T) ≫ composition A D K X Z T = _
    rw [composition_assoc, Iso.inv_hom_id_assoc]

/-- 各辺がA上K-flatなら自由dg圏の全HomもK-flat。 -/
lemma homKFlat (K : ComplexQuiver A D) (hK : ∀ x y, complexKFlat A (K x y)) :
    localHomKFlat A (Objects A D K) := by
  intro x y
  exact homComplex_kFlat A D K hK x y

variable (E : Type w) [DGCategory A E]

/-- 対象写像と辺のchain mapから自由dg圏上のdg関手を構成する。 -/
def lift (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) : DGFunctor A (Objects A D K) E where
  obj X := o X
  map X Y := homEvaluation A D E K o f X Y
  map_id X := unitInclusion_homEvaluation A D E K o f X
  map_comp X Y Z := homEvaluation_composition A D E K o f X Y Z

lemma lift_edge (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) (x y : D) :
    edgeInclusion A D K x y ≫ (lift A D E K o f).map x y = f x y :=
  edgeInclusion_homEvaluation A D E K o f x y

end SerrePositivity.DifferentialGraded.FreeDGCategory
end

end Category

/-! ## Reconstruction（旧 SerrePositivity/DifferentialGraded/Resolution/Free/Reconstruction.lean） -/

/-! # 自由dg圏上のdg関手の生成辺からの再構成

## 概要
自由dg圏上のdg関手の生成辺からの再構成。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Reconstruction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]
  (E : Type w) [DGCategory A E]

lemma composition_edge_path (K : ComplexQuiver A D) (x b y : D) (w : List D) :
    (edgeInclusion A D K x b ⊗ₘ pathInclusion A D K b y (.inr w)) ≫
        composition A D K x b y = pathInclusion A D K x y (.inr (b :: w)) := by
  have h := composition_nonempty A D K x b y [] w
  exact h.trans (Category.id_comp _)

lemma functor_word (K : ComplexQuiver A D) (F : DGFunctor A (Objects A D K) E)
    (w : List D) (x y : D) :
    pathInclusion A D K x y (.inr w) ≫ F.map x y =
      wordEvaluation A D E K F.obj (fun x y => edgeInclusion A D K x y ≫ F.map x y) w x y := by
  induction w generalizing x with
  | nil => rfl
  | cons b w ih =>
    have hc := F.map_comp x b y
    change composition A D K x b y ≫ F.map x y =
      (F.map x b ⊗ₘ F.map b y) ≫ eComp (Complex A) (F.obj x) (F.obj b) (F.obj y) at hc
    rw [← composition_edge_path A D K x b y w, Category.assoc, hc]
    rw [← Category.assoc, tensorHom_comp_tensorHom, ih]
    rfl

lemma functor_path (K : ComplexQuiver A D) (F : DGFunctor A (Objects A D K) E)
    {x y : D} (p : PathIndex D x y) :
    pathInclusion A D K x y p ≫ F.map x y =
      pathEvaluation A D E K F.obj (fun x y => edgeInclusion A D K x y ≫ F.map x y) p := by
  cases p with
  | inl h =>
    rcases h with ⟨h⟩
    subst y
    exact F.map_id x
  | inr w => exact functor_word A D E K F w x y

lemma homEvaluation_reconstruction (K : ComplexQuiver A D)
    (F : DGFunctor A (Objects A D K) E) (x y : D) :
    homEvaluation A D E K F.obj (fun x y => edgeInclusion A D K x y ≫ F.map x y) x y =
      F.map x y := by
  apply homComplex_ext A D K x y
  intro p
  exact (pathInclusion_homEvaluation A D E K F.obj _ x y p).trans
    (functor_path A D E K F p).symm

lemma lift_reconstruction (K : ComplexQuiver A D) (F : DGFunctor A (Objects A D K) E) :
    lift A D E K F.obj (fun x y => edgeInclusion A D K x y ≫ F.map x y) = F := by
  apply EnrichedFunctor.ext (Complex A)
    (F := lift A D E K F.obj (fun x y => edgeInclusion A D K x y ≫ F.map x y))
    (G := F) (fun _ => rfl)
  intro x y
  change homEvaluation A D E K F.obj _ x y ≫ eqToHom (by rfl) = F.map x y
  rw [eqToHom_refl, Category.comp_id]
  exact homEvaluation_reconstruction A D E K F x y

end SerrePositivity.DifferentialGraded.FreeDGCategory
end

end Reconstruction

/-! ## Universal（旧 SerrePositivity/DifferentialGraded/Resolution/Free/Universal.lean） -/

/-! # 自由dg圏の対象写像・生成辺に関する厳密普遍性

## 概要
自由dg圏の対象写像・生成辺に関する厳密普遍性。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Universal

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) [DGCategory A E]

/-- 自由dg圏への入力。対象写像と各生成辺のchain mapだけを指定する。 -/
structure GeneratorMap (K : ComplexQuiver A D) where
  obj : D → E
  map : ∀ x y, K x y ⟶ (obj x ⟶[Complex A] obj y)

variable [Small.{u} D]

def restrict (K : ComplexQuiver A D) (F : DGFunctor A (Objects A D K) E) :
    GeneratorMap A D E K where
  obj := F.obj
  map x y := edgeInclusion A D K x y ≫ F.map x y

def extend (K : ComplexQuiver A D) (g : GeneratorMap A D E K) : DGFunctor A (Objects A D K) E :=
  lift A D E K g.obj g.map

lemma extend_restrict (K : ComplexQuiver A D) (F : DGFunctor A (Objects A D K) E) :
    extend A D E K (restrict A D E K F) = F := lift_reconstruction A D E K F

lemma restrict_extend (K : ComplexQuiver A D) (g : GeneratorMap A D E K) :
    restrict A D E K (extend A D E K g) = g := by
  cases g with
  | mk o f =>
    change (⟨o, fun x y => edgeInclusion A D K x y ≫ (lift A D E K o f).map x y⟩ :
      GeneratorMap A D E K) = ⟨o, f⟩
    congr 1
    funext x y
    exact lift_edge A D E K o f x y

/-- 自由dg圏上のdg関手と対象・辺の入力データの型の厳密な同値。 -/
def universalEquiv (K : ComplexQuiver A D) :
    DGFunctor A (Objects A D K) E ≃ GeneratorMap A D E K where
  toFun := restrict A D E K
  invFun := extend A D E K
  left_inv := extend_restrict A D E K
  right_inv := restrict_extend A D E K

lemma extension_unique (K : ComplexQuiver A D) (g : GeneratorMap A D E K)
    (F : DGFunctor A (Objects A D K) E) (h : restrict A D E K F = g) :
    F = extend A D E K g := by
  rw [← h, extend_restrict]

end SerrePositivity.DifferentialGraded.FreeDGCategory
end

end Universal
