module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Index
public import Mathlib.CategoryTheory.Elements

/-!
# Reedy圏上の図式の要素の圏にReedy構造を構成する

## 概要
Reedy圏上の図式の要素の圏にReedy構造を構成する。
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
[棚卸し m0263][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0263
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Reedy structures on actual categories of elements

The projection need not be full or injective on objects. A factorization
lifts uniquely because its middle element is forced by its left arrow.
This applies to the category of simplices without a smallness assumption.
-/

@[expose] public section
universe v u w t
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] (F : J ⥤ Type w)
  {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α)

abbrev elementsInverse := inverse.inverseImage (Functor.Elements.π F)
abbrev elementsDirect := direct.inverseImage (Functor.Elements.π F)

omit [inverse.IsMultiplicative] [direct.IsMultiplicative] in
lemma elements_identities {x y : F.Elements} (f : x ⟶ y)
    (h : MorphismProperty.identities J f.hom) : MorphismProperty.identities F.Elements f := by
  rcases x with @⟨X, x⟩
  rcases y with @⟨Y, y⟩
  rcases f with ⟨f, hf⟩
  cases h
  have hxy : x = y := by
    change F.map (𝟙 X) x = y at hf
    rw [F.map_id] at hf
    exact hf
  subst y
  exact MorphismProperty.ofHoms.mk _

abbrev elementsForgetFactorization {x y : F.Elements} {f : x ⟶ y}
    (q : MorphismProperty.MapFactorizationData
      (elementsInverse (inverse := inverse) F) (elementsDirect (direct := direct) F) f) :
    MorphismProperty.MapFactorizationData inverse direct f.hom where
  Z := q.Z.obj
  i := q.i.hom
  p := q.p.hom
  fac := congrArg (fun f => f.hom) q.fac
  hi := q.hi
  hp := q.hp

omit [inverse.IsMultiplicative] [direct.IsMultiplicative] in
lemma elementsForgetFactorization_injective {x y : F.Elements} (f : x ⟶ y) :
    Function.Injective
      (elementsForgetFactorization (inverse := inverse) (direct := direct) F (f := f)) := by
  rintro ⟨@⟨Z, z⟩, ⟨i, hi⟩, ⟨p, hp⟩, h, hI, hP⟩
    ⟨@⟨Z', z'⟩, ⟨i', hi'⟩, ⟨p', hp'⟩, h', hI', hP'⟩ hq
  dsimp [elementsForgetFactorization] at hq
  cases hq
  have hz : z = z' := hi.symm.trans hi'
  subst z'
  rfl

def elementsFactorization {x y : F.Elements} (f : x ⟶ y) :
    MorphismProperty.MapFactorizationData
      (elementsInverse (inverse := inverse) F) (elementsDirect (direct := direct) F) f := by
  let q := r.mapFactorizationData f.hom
  refine ⟨Functor.elementsMk F q.Z (F.map q.i x.val), ⟨q.i, rfl⟩, ⟨q.p, ?_⟩, ?_, q.hi, q.hp⟩
  · rw [← ConcreteCategory.comp_apply, ← F.map_comp, q.fac]
    exact f.map_val
  · exact Functor.Elements.hom_ext q.fac

/- 旧宣言の技術注記：
Unique base factorizations lift to actual unique element factorizations.
-/
/-- Reedy圏上の図式の要素の圏にReedy構造を構成する。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
Reedy境界の添字と比較写像を明示し、境界の普遍性を照合する。
次数ごとの構成を既存の低次数の系と整合させる。
-/
def elementsReedy : ReedyStructure
    (elementsInverse (inverse := inverse) F) (elementsDirect (direct := direct) F) α where
  deg x := r.deg x.obj
  lt₁ f hf hf' := r.lt₁ f.hom hf (fun h => hf' (elements_identities F f h))
  lt₂ f hf hf' := r.lt₂ f.hom hf (fun h => hf' (elements_identities F f h))
  nonempty_unique f := by
    have := r.subsingleton_mapFactorizationData f.hom
    have : Subsingleton (MorphismProperty.MapFactorizationData
        (elementsInverse (inverse := inverse) F) (elementsDirect (direct := direct) F) f) :=
      (elementsForgetFactorization_injective F f).subsingleton
    exact ⟨{
      default := elementsFactorization F r f
      uniq := fun _ => Subsingleton.elim _ _ }⟩

end SerrePositivity.Reedy
