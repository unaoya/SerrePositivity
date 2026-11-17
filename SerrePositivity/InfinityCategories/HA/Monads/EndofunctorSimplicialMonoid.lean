module

public import SerrePositivity.InfinityCategories.HA.Monads.EndofunctorComposition
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic

/-!
概要：自己関手の全合成を、次数ごとのモノイドと全ての単体作用に表示する。
方針：内部モノイドを関手圏のモノイドとして評価し、各単体作用をモノイド射にする。
規約：次数 n の元は全 Fun(C,C) の n 単体。h Fun の対象・射だけに切り詰めない。
使われ方：HA §4.7.2–§4.7.3、Proposition 4.7.3.3 の周囲の全合成。
Kerodon Remark 6.2.1.4（Tag 02EN）の h Fun へ忘却する前の合成を保持する。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：全自己関手の n 単体をモノイドとして表示する単体的モノイド。
方針：内部モノイドの次数別評価と Type の内部モノイドの表示を合成する。
規約：全ての face・degeneracy は実際のモノイド射。
使われ方：HA §4.7.2 の全合成を用いる高次の図式。 -/
def endofunctorSimplicialMonoid (C : SSet.{u}) : SimplicialObject MonCat.{u} :=
  letI := endofunctorCompositionMonObj C
  Monoidal.MonFunctorCategoryEquivalence.functorObj (EndofunctorSpace C) ⋙
    MonTypeEquivalenceMon.functor

/-- 概要：次数別表示の台は元の全自己関手の単体である。
方針：評価の定義を展開する。規約：型の同一視だけであり高次情報を捨てない。
使われ方：HA Proposition 4.7.3.3 の同じ関手準圏との照合。 -/
lemma endofunctorSimplicialMonoid_obj (C : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    ↥((endofunctorSimplicialMonoid C).obj n) = (EndofunctorSpace C).obj n := rfl

/-- 概要：次数別表示の単体作用は元の自己関手単体集合の作用と一致する。
方針：内部モノイドの評価射の定義を使う。規約：任意の単体圏の射を量化する。
使われ方：HA §4.7.2–§4.7.3 の全自然性の照合。 -/
lemma endofunctorSimplicialMonoid_map_apply (C : SSet.{u})
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (EndofunctorSpace C).obj n) :
    (endofunctorSimplicialMonoid C).map f x = (EndofunctorSpace C).map f x := rfl

/-- 概要：各次数の単位は指定された恒等関手の単体。
方針：内部モノイドの単位の評価を計算する。規約：全次数で成り立つ。
使われ方：HA §4.7.2 の単位と単体作用の照合。 -/
lemma endofunctorSimplicialMonoid_one (C : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (1 : (endofunctorSimplicialMonoid C).obj n) =
      (endofunctorUnit C).app n PUnit.unit := rfl

/-- 概要：各次数の積は元の全合成の同じ次数での評価。
方針：内部モノイドの積の定義を展開する。規約：第一因子の後に第二因子を適用する。
使われ方：HA Proposition 4.7.3.3 の指定合成の照合。 -/
lemma endofunctorSimplicialMonoid_mul (C : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (x y : (endofunctorSimplicialMonoid C).obj n) :
    x * y = (endofunctorComposition C).app n (x, y) := rfl

end SerrePositivity.InfinityCategories.HA.Monads
