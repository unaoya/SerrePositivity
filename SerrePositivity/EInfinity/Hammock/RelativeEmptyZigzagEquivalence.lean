module

public import SerrePositivity.EInfinity.Hammock.EmptyZigzag
public import SerrePositivity.EInfinity.Hammock.Unit
public import SerrePositivity.EInfinity.Hammock.RelativeFixedZigzagFunctor

/-!
# 対象単射な相対関手による元の空語圏の同値

概要：元の固定端点と全単体作用素を保持する。
方針：一頂点の一意性と実際の相対関手・対角比較を使う。
規約：通常の hammock augmentation の弱同値性を仮定しない。
使われ方：DK5.7の全語の帰納基底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.Zigzag.Relative
open CategoryTheory
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {W : MorphismProperty C} [W.IsMultiplicative]
  {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) {X Y : C} {X' Y' : D}
  (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
instance empty_fixed_faithful : (fixedFunctor (w := Word.empty) F hX hY).Faithful where
  map_injective _ := Subsingleton.elim _ _
instance empty_fixed_full : (fixedFunctor (w := Word.empty) F hX hY).Full where
  map_surjective {S T} _ := ⟨eqToHom (Subsingleton.elim S T), Subsingleton.elim _ _⟩
lemma empty_fixed_essSurj (hF : Function.Injective F.functor.obj) :
    (fixedFunctor (w := Word.empty) F hX hY).EssSurj := by
  constructor
  intro S
  have h : X = Y := hF (hX.trans ((empty_endpoints S).trans hY.symm))
  let T : Zigzag W Word.empty X Y := EndpointChange.obj rfl h (emptyObj W X)
  exact ⟨T, ⟨eqToIso (Subsingleton.elim _ _)⟩⟩
lemma empty_fixed_isEquivalence (hF : Function.Injective F.functor.obj) :
    (fixedFunctor (w := Word.empty) F hX hY).IsEquivalence := by
  have := empty_fixed_essSurj F hX hY hF
  exact {}
end SerrePositivity.EInfinity.Hammock.Zigzag.Relative
