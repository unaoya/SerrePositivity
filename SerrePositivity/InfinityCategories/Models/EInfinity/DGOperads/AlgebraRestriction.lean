module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Morphism
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionCoefficient

/-!
模型。文献の定義との比較は後で
# オペラッド射に沿う代数の制限

概要：BM §1 の代数構造をオペラッド射の前合成で制限する。
方針：単位・部分合成保存と係数自然性を用いて代数の公理を移す。
規約：底の複体と射は変えず、arity 零も保つ。
使われ方：Com 代数を E → Com に沿って E 代数にする。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- 概要：Q 代数をオペラッド射 P → Q に沿って制限する（BM §1）。
方針：各作用の係数へ射を前合成し、単位と合成の保存を用いる。
規約：底の複体と全 arity の入力テンソル冪は同一。
使われ方：離散可換代数の E 代数構造。 -/
def restrictAlgebraObj (f : P ⟶ Q) (X : Q.Algebra) : P.Algebra where
  carrier := X.carrier
  action n := (f.map.app (_root_.SerrePositivity.FiniteBijection.of n) ▷ power X.carrier n) ≫ X.action n
  equivariance n σ := by
    change (P.sequence.map _ ⊗ₘ _) ≫
      (f.map.app _ ▷ power X.carrier n) ≫ X.action n = _
    rw [tensorHom_comp_whiskerRight_assoc, f.map.naturality]
    rw [← whiskerRight_comp_tensorHom_assoc]
    exact congrArg (fun h => (f.map.app (_root_.SerrePositivity.FiniteBijection.of n) ▷ power X.carrier n) ≫ h)
      (X.equivariance n σ)
  unit_action := by
    change (P.unit ▷ power X.carrier 1) ≫ (f.map.app _ ▷ power X.carrier 1) ≫
      X.action 1 = _
    rw [← comp_whiskerRight_assoc, f.unit]
    exact X.unit_action
  comp_action m n i := by
    change (P.comp m n i ▷ power X.carrier (m + n)) ≫
      (f.map.app _ ▷ power X.carrier (m + n)) ≫ X.action (m + n) = _
    rw [← comp_whiskerRight_assoc, f.comp, comp_whiskerRight, Category.assoc,
      X.comp_action]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionComposition_coeff (f.map.app _) (f.map.app _) m n i
      (X.action n) (X.action (m + 1))

/-- 概要：代数の射も同じ底の射のまま制限する（BM §1）。
方針：係数射と底の射の交換則から作用保存を移す。
規約：arity 零の作用も保存する。
使われ方：離散可換代数の射を E 代数の射へ送る。 -/
def restrictAlgebraMap (f : P ⟶ Q) {X Y : Q.Algebra} (g : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictAlgebraObj f X ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictAlgebraObj f Y where
  hom := g.hom
  comm n := by
    change ((f.map.app _ ▷ power X.carrier n) ≫ X.action n) ≫ g.hom =
      (𝟙 _ ⊗ₘ _root_.SerrePositivity.TensorPowers.map g.hom n) ≫
        (f.map.app _ ▷ power Y.carrier n) ≫ Y.action n
    rw [Category.assoc, g.comm]
    simp only [id_tensorHom]
    rw [whisker_exchange_assoc]
    rfl

/-- 概要：オペラッド射に沿う代数の制限関手（BM §1）。
方針：制限した対象と底の同じ射を束ねる。
規約：忘却後は元の複体と射を厳密に保つ。
使われ方：Com 代数の E 代数化の関手性。 -/
def restrictAlgebra (f : P ⟶ Q) : Q.Algebra ⥤ P.Algebra where
  obj := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictAlgebraObj f
  map := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictAlgebraMap f
  map_id X := by apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext; rfl
  map_comp g h := by apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext; rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
