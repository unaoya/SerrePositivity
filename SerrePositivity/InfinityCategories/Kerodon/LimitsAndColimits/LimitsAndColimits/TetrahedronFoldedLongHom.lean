module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TetrahedronPathFold
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TetrahedronLongHomReplacement

/-!
概要：同じ厳密合成値を持つ三単体の長い Hom を、二内面で一致する形に正規化する。
方針：二つの内部合成面が同じ定値であるとき、論理和による path の畳み込みを使う。
規約：内部合成面の定値性は別途、指定された厳密合成面から回収する。
使われ方：Ind-S (9b) の native Hom 制御の有限 enriched 部分。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits


/-- 内部合成面の共通の定値は、第二合成 path での値そのもの。 -/
lemma tetrahedronLongHom_composite_value {H : SSet.{u}}
    (m : nerve (Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3)) ⟶ H)
    (c : H _⦋0⦌)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 4)) (ULift.up 2) (ULift.up 3) ≫ m = SSet.const c) :
    m.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronFoldCompositePath) = c := by
  let p : Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 2) :=
    { I := {k | k.down = 0 ∨ k.down = 2}
      left := Or.inl rfl
      right := Or.inr rfl
      left_le := fun _ _ => Fin.zero_le _
      le_right := by intro k hk; change k.down ≤ 2; rcases hk with h | h <;> omega }
  let q : Path (ULift.up (2 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) :=
    { I := {k | k.down = 2 ∨ k.down = 3}
      left := Or.inl rfl
      right := Or.inr rfl
      left_le := by intro k hk; change 2 ≤ k.down; rcases hk with h | h <;> omega
      le_right := fun _ _ => Fin.le_last _ }
  let r : Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) :=
    { I := p.I ∪ q.I
      left := Or.inl p.left
      right := Or.inr q.right
      left_le := fun _ _ => Fin.zero_le _
      le_right := fun _ _ => Fin.le_last _ }
  have hpq : r = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronFoldCompositePath := by
    apply SimplicialThickening.Path.ext
    ext k
    change ((k.down = 0 ∨ k.down = 2) ∨ k.down = 2 ∨ k.down = 3) ↔
      (k.down = 0 ∨ k.down = 3 ∨ k.down = 2)
    tauto
  let z : (nerve (Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 2)) ⊗
      nerve (Path (ULift.up (2 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3))) _⦋0⦌ :=
    (ComposableArrows.mk₀ p, ComposableArrows.mk₀ q)
  have hh := congrArg (fun F => F.app (Opposite.op ⦋0⦌) z) hc
  change m.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ r) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant c 0 at hh
  simpa only [hpq, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] using hh

/-- 畳み込みは同じ二つの内部定値合成面を全次数で保持する。 -/
lemma tetrahedronFoldedLongHom_comp {H : SSet.{u}}
    (m : nerve (Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3)) ⟶ H)
    (c : H _⦋0⦌)
    (hc : ∀ j : Fin 4, 0 < j → j < 3 →
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 4)) (ULift.up j) (ULift.up 3) ≫ m = SSet.const c)
    (j : Fin 4) (hj₀ : 0 < j) (hj₃ : j < 3) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 4)) (ULift.up j) (ULift.up 3) ≫
      nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronPathFold ≫ m =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 4)) (ULift.up j) (ULift.up 3) ≫ m := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronPathFold_comp j hj₀ hj₃,
    SSet.const_comp, tetrahedronLongHom_composite_value m c (hc 2 (by decide) (by decide)),
    hc j hj₀ hj₃]

/-- 同じ定値合成面を持つ三単体の全 Hom を畳み込んだ実三単体。 -/
def tetrahedronWithFoldedLongHom {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (t : (SimplicialNerve C) _⦋3⦌)
    (c : (SimplicialCategory.sHom (t.obj ⟨ULift.up 0⟩) (t.obj ⟨ULift.up 3⟩)) _⦋0⦌)
    (hc : ∀ j : Fin 4, 0 < j → j < 3 →
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 4)) (ULift.up j) (ULift.up 3) ≫
        t.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩ = SSet.const c) :
    (SimplicialNerve C) _⦋3⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronReplaceLongHom t (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronPathFold ≫ t.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩)
    (fun j hj₀ hj₃ => (tetrahedronFoldedLongHom_comp _ c hc j hj₀ hj₃).trans
      (t.map_comp ⟨ULift.up 0⟩ ⟨ULift.up j⟩ ⟨ULift.up 3⟩))


variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
variable (t : (SimplicialNerve C) _⦋3⦌)
variable (c : (SimplicialCategory.sHom (t.obj ⟨ULift.up 0⟩) (t.obj ⟨ULift.up 3⟩)) _⦋0⦌)
variable (hc : ∀ j : Fin 4, 0 < j → j < 3 →
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 4)) (ULift.up j) (ULift.up 3) ≫
    t.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩ = SSet.const c)

/-- 正規化は零番面を厳密に保持する。 -/
lemma tetrahedronWithFoldedLongHom_face_zero :
    (SimplicialNerve C).δ (0 : Fin 4) (tetrahedronWithFoldedLongHom t c hc) =
      (SimplicialNerve C).δ (0 : Fin 4) t :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronReplaceLongHom_face_zero t _ _

/-- 正規化は三番面を厳密に保持する。 -/
lemma tetrahedronWithFoldedLongHom_face_three :
    (SimplicialNerve C).δ (3 : Fin 4) (tetrahedronWithFoldedLongHom t c hc) =
      (SimplicialNerve C).δ (3 : Fin 4) t :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronReplaceLongHom_face_three t _ _

/-- 正規化は元の一番面を全 native Hom とともに厳密に保持する。 -/
lemma tetrahedronWithFoldedLongHom_face_one :
    (SimplicialNerve C).δ (1 : Fin 4) (tetrahedronWithFoldedLongHom t c hc) =
      (SimplicialNerve C).δ (1 : Fin 4) t := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronReplaceLongHom_face_one t _ _
  change nerveMap _ ≫ nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronPathFold ≫
      t.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩ =
    nerveMap _ ≫ t.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩
  rw [← Category.assoc]
  have hh := congrArg (fun F :
    Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2) ⥤
      Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) => nerveMap F)
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronPathFold_face_one
  exact hh =≫ t.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩

/-- 正規化した長い Hom は畳み込みで不変。 -/
lemma tetrahedronWithFoldedLongHom_invariant :
    nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronPathFold ≫
      (tetrahedronWithFoldedLongHom t c hc).map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩ =
      (tetrahedronWithFoldedLongHom t c hc).map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩ := by
  change nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronPathFold ≫
    (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronPathFold ≫ t.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩) =
    nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronPathFold ≫ t.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩
  rw [← Category.assoc]
  have hh := congrArg (fun F :
    Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) ⥤
      Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) => nerveMap F)
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronPathFold_idempotent
  exact hh =≫ t.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
