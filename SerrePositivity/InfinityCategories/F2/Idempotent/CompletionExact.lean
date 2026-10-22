module

public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionColimits
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionPointed
public import SerrePositivity.InfinityCategories.Stable.ExactFunctor

/-!
概要：元の任意の冪等完備化は、全普遍四角形と零角の fiber/cofiber 列を保存する。
方針：全極限・余極限保存を元の cospan・span の普遍錐に適用する。
規約：標的の安定性を前提にせず、元の関手の完全性を証明する。
使われ方：HA 1.1.3.7 の元の四角形の移送と元の Yoneda 因子化の完全性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の任意の冪等完備化は、元の指定引き戻し四角形そのものを保存する。 -/
lemma IsIdempotentCompletion.preservesPullbackSquare {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : IsIdempotentCompletion f)
    (F : Δ[1] ⊗ Δ[1] ⟶ C) (hF : IsPullbackSquare F) : IsPullbackSquare (F ≫ f) := by
  have h := IsIdempotentCompletion.mapJoinCone_isLimit f hf (pullbackCone F) hF
  exact (isLimitCone_iff_of_diagram_eq
    (Category.assoc _ _ _) (Category.assoc _ _ _)).mp h

/-- 元の任意の冪等完備化は、元の指定押し出し四角形そのものを保存する。 -/
lemma IsIdempotentCompletion.preservesPushoutSquare {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : IsIdempotentCompletion f)
    (F : Δ[1] ⊗ Δ[1] ⟶ C) (hF : IsPushoutSquare F) : IsPushoutSquare (F ≫ f) := by
  have h := IsIdempotentCompletion.mapJoinCocone_isColimit f hf (pushoutCocone F) hF
  exact (isColimitCone_iff_of_val_eq (mapJoinCocone f (pushoutCocone F))
    (pushoutCocone (F ≫ f)) (Category.assoc _ _ _)).mp h

/-- 元の任意の冪等完備化は、零対象を持つ元の関手として完全。 -/
lemma IsIdempotentCompletion.isExactFunctor {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : IsIdempotentCompletion f) :
    IsExactFunctor f where
  preservesZero _ hz := IsIdempotentCompletion.map_isZeroVertex f hf hz
  preservesCofiber t ht := IsIdempotentCompletion.preservesPushoutSquare f hf t.square ht

/-- 元の任意の冪等完備化は、標的の安定性を仮定せず元の fiber 列も保存する。 -/
lemma IsIdempotentCompletion.preservesFiber {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : IsIdempotentCompletion f)
    (t : ZeroTriangle C) (ht : IsFiberSequence t) :
    IsFiberSequence (t.map f (fun _ hz ↦ IsIdempotentCompletion.map_isZeroVertex f hf hz)) :=
  IsIdempotentCompletion.preservesPullbackSquare f hf t.square ht

/-- 元の全 Yoneda の冪等完備化への因子化は、標的の安定性を仮定せず完全。 -/
instance idemYoneda_isExactFunctor (C : SSet.{u}) [Quasicategory C] :
    IsExactFunctor (idemYoneda C) :=
  IsIdempotentCompletion.isExactFunctor (idemYoneda C) (idemYoneda_isIdempotentCompletion C)

end SerrePositivity.InfinityCategories.F2.Idempotent
