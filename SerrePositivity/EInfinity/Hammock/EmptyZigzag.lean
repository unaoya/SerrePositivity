module

public import SerrePositivity.EInfinity.Hammock.ZigzagExt

/-!
# 元の空語の対象と縦射の一意性

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
namespace SerrePositivity.EInfinity.Hammock.Zigzag
open CategoryTheory
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {X Y : C}
omit [W.IsMultiplicative] in
lemma empty_endpoints (S : Zigzag W Word.empty X Y) : X = Y :=
  S.first.symm.trans S.last
instance empty_subsingleton : Subsingleton (Zigzag W Word.empty X Y) := by
  constructor
  intro S T
  refine object_ext S T (fun j => ?_) (fun i => Fin.elim0 i)
  have hj : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  exact (congrArg S.vertex hj).trans (S.first.trans (T.first.symm.trans
    (congrArg T.vertex hj).symm))
instance empty_hom_subsingleton (S T : Zigzag W Word.empty X Y) : Subsingleton (S ⟶ T) := by
  constructor
  intro f g
  apply hom_ext
  intro j
  have hj : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  cases hj
  exact f.first.trans g.first.symm
instance empty_hom_nonempty (S T : Zigzag W Word.empty X Y) : Nonempty (S ⟶ T) :=
  ⟨eqToHom (Subsingleton.elim S T)⟩
end SerrePositivity.EInfinity.Hammock.Zigzag
