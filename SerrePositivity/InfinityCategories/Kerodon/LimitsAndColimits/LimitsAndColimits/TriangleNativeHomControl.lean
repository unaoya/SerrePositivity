module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleLongHomReplacement
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TrianglePathInterval

/-!
概要：全長 Hom の合成端の指定から二単体を構成する有限部分。
方針：唯一の内部合成 path が全 path に定値であることを全次数で計算する。
規約：二短辺と全 native Hom の写像を保持し、単なる長辺一致へ弱めない。
使われ方：Ind-S (9) の全族構成における頂点の厳密回収。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits


/-- 二単体の内部合成は全 path に定値。 -/
lemma trianglePathCompMap_eq_const :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 1) (ULift.up 2) =
      SSet.const (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u}) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨p, q⟩
  apply CategoryTheory.Functor.ext (fun i => ?_)
  apply SimplicialThickening.Path.ext
  ext ⟨k⟩
  change (ULift.up k ∈ (p.obj i).I ∪ (q.obj i).I) ↔
    (ULift.up k : ULift.{u} (Fin 3)) ∈ Set.univ
  fin_cases k
  · simp [(p.obj i).left]
  · simp [(p.obj i).right]
  · simp [(q.obj i).right]

/-- 合成端の一点の指定は内部合成面の全次数の指定を与える。 -/
lemma triangleLongHom_comp_of_full_value {H : SSet.{u}}
    (m : nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u} ⟶ H) (c : H _⦋0⦌)
    (hc : m.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath) = c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 1) (ULift.up 2) ≫ m =
      SSet.const c := by
  rw [trianglePathCompMap_eq_const, SSet.const_comp, hc]

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 同じ合成端を持つ任意の全長 Hom を、同じ二短辺の実二単体に入れる。 -/
def triangleWithNativeLongHom (t : (SimplicialNerve C) _⦋2⦌)
    (m : nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u} ⟶
      SimplicialCategory.sHom (t.obj ⟨ULift.up 0⟩) (t.obj ⟨ULift.up 2⟩))
    (hcomp : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 3)) (ULift.up 1) (ULift.up 2) ≫ m =
      (t.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩ ⊗ₘ t.map ⟨ULift.up 1⟩ ⟨ULift.up 2⟩) ≫
        eComp SSet (t.obj ⟨ULift.up 0⟩) (t.obj ⟨ULift.up 1⟩) (t.obj ⟨ULift.up 2⟩)) :
    (SimplicialNerve C) _⦋2⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleReplaceLongHom t m (by
    intro j hj₀ hj₂
    have hj : j = 1 := by omega
    subst j
    exact hcomp)

variable (t : (SimplicialNerve C) _⦋2⦌)
  (m : nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u} ⟶
    SimplicialCategory.sHom (t.obj ⟨ULift.up 0⟩) (t.obj ⟨ULift.up 2⟩))
  (hcomp : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 3)) (ULift.up 1) (ULift.up 2) ≫ m =
    (t.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩ ⊗ₘ t.map ⟨ULift.up 1⟩ ⟨ULift.up 2⟩) ≫
      eComp SSet (t.obj ⟨ULift.up 0⟩) (t.obj ⟨ULift.up 1⟩) (t.obj ⟨ULift.up 2⟩))

lemma triangleWithNativeLongHom_first :
    (SimplicialNerve C).δ (2 : Fin 3) (triangleWithNativeLongHom t m hcomp) =
      (SimplicialNerve C).δ (2 : Fin 3) t := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleReplaceLongHom_face_two t m _

lemma triangleWithNativeLongHom_last :
    (SimplicialNerve C).δ (0 : Fin 3) (triangleWithNativeLongHom t m hcomp) =
      (SimplicialNerve C).δ (0 : Fin 3) t := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleReplaceLongHom_face_zero t m _

lemma triangleWithNativeLongHom_native :
    (triangleWithNativeLongHom t m hcomp).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩ = m :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleReplaceLongHom_map t m _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
