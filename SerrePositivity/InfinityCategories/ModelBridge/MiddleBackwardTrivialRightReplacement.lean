module

public import SerrePositivity.InfinityCategories.ModelBridge.MiddleBackwardTrivialCofibration
public import SerrePositivity.InfinityCategories.ModelBridge.MiddleBackwardFamilyPrecomp

/-!
# 元の中央自明 cofibration の全部分圏上の右置換

概要：元の全部分圏から右置換図式を構成し、元の包含からの実際の unit を得る。
方針：元の抽出図式を包含へ前合成し、再構成との厳密な同定で元の始域へ戻す。
規約：中央の実際の列の自明性を用いる。恒等列の挿入との同定は後続。
使われ方：中央 backward 恒等列の挿入の第二の nerve 比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.TrivialCofibration
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}

def sourceFamily : Family (Objects (C := C) (n := n) (m := m) (X := X) (Y := Y)) C n m X Y :=
  Extract.family.precomp inclusion

lemma sourceFamily_middle_trivial (S : Objects (C := C) (n := n) (m := m) (X := X) (Y := Y)) :
    trivialCofibrations C (sourceFamily.middle.app S) := by
  have h := (Extract.family.middleColumn_property (trivialCofibrations C) S.obj)
  change trivialCofibrations C ((Extract.rebuilt S.obj).arrow (Positions.middleColumn n m)) ↔
    trivialCofibrations C (sourceFamily.middle.app S) at h
  rw [Extract.rebuilt_eq] at h
  exact h.mp S.property

def rightReplacement : Objects (C := C) (n := n) (m := m) (X := X) (Y := Y) ⥤
    Zigzag (weakEquivalences C) (word n m) X Y :=
  sourceFamily.pushoutFunctor sourceFamily_middle_trivial

def rightUnit : inclusion (C := C) (n := n) (m := m) (X := X) (Y := Y) ⟶ rightReplacement :=
  Functor.whiskerLeft inclusion Extract.rebuildIso.inv ≫
    sourceFamily.pushoutUnit sourceFamily_middle_trivial

end SerrePositivity.EInfinity.Hammock.MiddleBackward.TrivialCofibration
