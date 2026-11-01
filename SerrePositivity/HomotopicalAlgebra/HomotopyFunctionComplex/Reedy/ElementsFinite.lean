module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Elements
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# 要素の圏のlatching添字の有限性を元の境界の有限性から導く

## 概要
要素の圏のlatching添字の有限性を元の境界の有限性から導く。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
Reedy境界の添字と比較写像を明示し、境界の普遍性を照合する。
次数ごとの構成を既存の低次数の系と整合させる。

## 規約と注意
圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
表示された圏や比較射を、局所化後の同型だけで置き換えない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0264][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0264
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Finite boundary indices in categories of elements

Outgoing element arrows are determined by their underlying arrows.
Incoming arrows are also determined when the relevant structure maps are
injective. Finite base boundary indices therefore give finite element
boundary indices, independently of the size of the sets of elements.
-/

@[expose] public section
universe v u w t
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] (F : J ⥤ Type w)

/-- Lift every base arrow out of an element by taking its actual image. -/
def elementsUnderLift (x : F.Elements) (q : Under x.obj) : Under x :=
  Under.mk (Functor.Elements.homMk (y := F.elementsMk q.right (F.map q.hom x.val)) q.hom rfl)

lemma elementsUnderLift_post (x : F.Elements) (q : Under x) :
    elementsUnderLift F x ((Under.post (Functor.Elements.π F)).obj q) = q := by
  obtain ⟨y, f, rfl⟩ := Under.mk_surjective q
  rcases y with @⟨Y, y⟩
  rcases f with ⟨f, hf⟩
  change x.obj ⟶ Y at f
  change F.map f x.val = y at hf
  subst y
  rfl

lemma elementsUnderPost_injective (x : F.Elements) :
    Function.Injective (Under.post (Functor.Elements.π F) (X := x)).obj :=
  Function.LeftInverse.injective (elementsUnderLift_post F x)

variable {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α)

abbrev elementsMatchingCode (x : F.Elements)
    (q : MatchingIndex (elementsReedy F r) x) : MatchingIndex r x.obj :=
  ⟨(Under.post (Functor.Elements.π F)).obj q.obj, q.property.1,
    fun h => q.property.2 (elements_identities F q.obj.hom h)⟩

lemma elementsMatchingCode_injective (x : F.Elements) :
    Function.Injective (elementsMatchingCode F r x) := by
  intro q q' h
  apply ObjectProperty.FullSubcategory.ext
  exact elementsUnderPost_injective F x (congrArg (fun q => q.obj) h)

abbrev elementsLatchingCode (x : F.Elements)
    (q : LatchingIndex (elementsReedy F r) x) : LatchingIndex r x.obj :=
  ⟨(Over.post (Functor.Elements.π F)).obj q.obj, q.property.1,
    fun h => q.property.2 (elements_identities F q.obj.hom h)⟩

lemma elementsLatchingCode_injective
    (hinj : ∀ {i j : J} (f : i ⟶ j), direct f → Function.Injective (F.map f))
    (x : F.Elements) : Function.Injective (elementsLatchingCode F r x) := by
  rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
  obtain ⟨y, f, rfl⟩ := Over.mk_surjective q
  obtain ⟨y', f', rfl⟩ := Over.mk_surjective q'
  rcases y with @⟨Y, y⟩
  rcases y' with @⟨Y', y'⟩
  rcases f with ⟨f, hf⟩
  rcases f' with ⟨f', hf'⟩
  have hb := congrArg (fun q => q.obj) h
  change Over.mk f = Over.mk f' at hb
  cases hb
  have hy : y = y' := hinj f hq.1 (hf.trans hf'.symm)
  subst y'
  rfl

instance elementsMatchingIndex_finite (x : F.Elements) [Finite (MatchingIndex r x.obj)] :
    Finite (MatchingIndex (elementsReedy F r) x) :=
  Finite.of_injective _ (elementsMatchingCode_injective F r x)

/-- 要素の圏のlatching添字の有限性を元の境界の有限性から導く。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
Reedy境界の添字と比較写像を明示し、境界の普遍性を照合する。
次数ごとの構成を既存の低次数の系と整合させる。
-/
lemma elementsLatchingIndex_finite
    (hinj : ∀ {i j : J} (f : i ⟶ j), direct f → Function.Injective (F.map f))
    (x : F.Elements) [Finite (LatchingIndex r x.obj)] :
    Finite (LatchingIndex (elementsReedy F r) x) :=
  Finite.of_injective _ (elementsLatchingCode_injective F r hinj x)

instance elementsLatchingHom_finite [∀ i j : J, Finite (i ⟶ j)]
    (x : F.Elements) (q q' : LatchingIndex (elementsReedy F r) x) : Finite (q ⟶ q') :=
  Finite.of_injective (fun f : q ⟶ q' => f.hom.left.hom) (by
    intro f g h
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact Functor.Elements.hom_ext h)

instance elementsMatchingHom_finite [∀ i j : J, Finite (i ⟶ j)]
    (x : F.Elements) (q q' : MatchingIndex (elementsReedy F r) x) : Finite (q ⟶ q') :=
  Finite.of_injective (fun f : q ⟶ q' => f.hom.right.hom) (by
    intro f g h
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    exact Functor.Elements.hom_ext h)

end SerrePositivity.Reedy
