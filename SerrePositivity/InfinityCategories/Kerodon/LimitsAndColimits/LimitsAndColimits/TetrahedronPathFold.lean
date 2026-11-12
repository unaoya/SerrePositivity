module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Path
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HornData
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.UnitComposition

/-!
概要：三単体の長い Hom の二内部座標を一つへ畳む。
方針：内部点 1 または 2 を含むときに 2 を含ませ、1 は除く。
規約：native Path の包含方向を使い、指定二面の全 Hom を比較する。
使われ方：Ind-S (9b) の欠面を制御するための有限座標。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 二内部点の論理和を第二内部点へ送る path。 -/
def tetrahedronPathFoldObj
    (P : Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3)) :
    Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) where
  I := {k | k.down = 0 ∨ k.down = 3 ∨
    k.down = 2 ∧ (ULift.up 1 ∈ P.I ∨ ULift.up 2 ∈ P.I)}
  left := Or.inl rfl
  right := Or.inr (Or.inl rfl)
  left_le _ _ := Fin.zero_le _
  le_right _ _ := Fin.le_last _

/-- 包含を保つ path の畳み込み関手。 -/
def tetrahedronPathFold :
    Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) ⥤
      Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) where
  obj := tetrahedronPathFoldObj
  map f := ⟨⟨⟨by
    intro k hk
    rcases hk with h | h | ⟨h, h₁ | h₂⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h, Or.inl (f.1.1.1 h₁)⟩)
    · exact Or.inr (Or.inr ⟨h, Or.inr (f.1.1.1 h₂)⟩)⟩⟩⟩

/-- 二つの内面の長い Hom を畳むと同じ path になる。 -/
lemma tetrahedronPathFold_faces_obj
    (P : Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) :
    tetrahedronPathFoldObj
      ((SimplicialThickening.functorMap (SimplexCategory.δ (1 : Fin 4)).toOrderHom.uliftMap
        ⟨ULift.up 0⟩ ⟨ULift.up 2⟩).obj P) =
    tetrahedronPathFoldObj
      ((SimplicialThickening.functorMap (SimplexCategory.δ (2 : Fin 4)).toOrderHom.uliftMap
        ⟨ULift.up 0⟩ ⟨ULift.up 2⟩).obj P) := by
  apply Path.ext
  ext k
  change (k.down = 0 ∨ k.down = 3 ∨ k.down = 2 ∧
    (ULift.up 1 ∈ _ '' P.I ∨ ULift.up 2 ∈ _ '' P.I)) ↔
    (k.down = 0 ∨ k.down = 3 ∨ k.down = 2 ∧
    (ULift.up 1 ∈ _ '' P.I ∨ ULift.up 2 ∈ _ '' P.I))
  have h₁ : (ULift.up 1 : ULift.{u} (Fin 4)) ∈
      (SimplexCategory.δ (1 : Fin 4)).toOrderHom.uliftMap '' P.I ↔ False := by
    constructor
    · rintro ⟨⟨l⟩, _, hl⟩
      fin_cases l <;> cases hl
    · simp
  have h₂ : (ULift.up 2 : ULift.{u} (Fin 4)) ∈
      (SimplexCategory.δ (2 : Fin 4)).toOrderHom.uliftMap '' P.I ↔ False := by
    constructor
    · rintro ⟨⟨l⟩, _, hl⟩
      fin_cases l <;> cases hl
    · simp
  have hm₁ : (ULift.up 2 : ULift.{u} (Fin 4)) ∈
      (SimplexCategory.δ (1 : Fin 4)).toOrderHom.uliftMap '' P.I ↔ ULift.up 1 ∈ P.I := by
    constructor
    · rintro ⟨⟨l⟩, hl, he⟩
      fin_cases l <;> first | exact hl | cases he
    · intro h
      exact ⟨ULift.up 1, h, rfl⟩
  have hm₂ : (ULift.up 1 : ULift.{u} (Fin 4)) ∈
      (SimplexCategory.δ (2 : Fin 4)).toOrderHom.uliftMap '' P.I ↔ ULift.up 1 ∈ P.I := by
    constructor
    · rintro ⟨⟨l⟩, hl, he⟩
      fin_cases l <;> first | exact hl | cases he
    · intro h
      exact ⟨ULift.up 1, h, rfl⟩
  simp only [h₁, h₂, hm₁, hm₂, false_or, or_false]

/-- 二つの内面の native Hom 包含は、畳み込みの後で厳密に一致する。 -/
lemma tetrahedronPathFold_faces :
    (SimplicialThickening.functorMap (SimplexCategory.δ (1 : Fin 4)).toOrderHom.uliftMap
      ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) ⋙ tetrahedronPathFold.{u} =
    (SimplicialThickening.functorMap (SimplexCategory.δ (2 : Fin 4)).toOrderHom.uliftMap
      ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) ⋙ tetrahedronPathFold.{u} := by
  exact CategoryTheory.Functor.ext (fun P => tetrahedronPathFold_faces_obj P)

/-- 第一内部点を避ける path は畳み込みで不変。 -/
lemma tetrahedronPathFoldObj_of_avoids
    (P : Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3))
    (hP : ULift.up 1 ∉ P.I) : tetrahedronPathFoldObj P = P := by
  apply Path.ext
  ext ⟨l⟩
  fin_cases l <;> simp [tetrahedronPathFoldObj, hP, P.left, P.right]

/-- 一番面の native Hom 全体は畳み込みで不変。 -/
lemma tetrahedronPathFold_face_one :
    (SimplicialThickening.functorMap (SimplexCategory.δ (1 : Fin 4)).toOrderHom.uliftMap
      ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) ⋙ tetrahedronPathFold.{u} =
    SimplicialThickening.functorMap (SimplexCategory.δ (1 : Fin 4)).toOrderHom.uliftMap
      ⟨ULift.up 0⟩ ⟨ULift.up 2⟩ := by
  apply CategoryTheory.Functor.ext (fun P => ?_)
  apply tetrahedronPathFoldObj_of_avoids
  rintro ⟨⟨l⟩, _, he⟩
  exact Fin.succAbove_ne (1 : Fin 4) l (congrArg ULift.down he)

/-- 第二内部点を経由する最小 path。 -/
def tetrahedronFoldCompositePath :
    Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) where
  I := {k | k.down = 0 ∨ k.down = 3 ∨ k.down = 2}
  left := Or.inl rfl
  right := Or.inr (Or.inl rfl)
  left_le _ _ := Fin.zero_le _
  le_right _ _ := Fin.le_last _

/-- 内部点を経由する合成の全 Hom は、畳み込み後に同じ第二合成点へ定値。 -/
lemma tetrahedronPathFold_comp (j : Fin 4) (hj₀ : 0 < j) (hj₃ : j < 3) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up j)
        (ULift.up 3) ≫ nerveMap tetrahedronPathFold =
      SSet.const (ComposableArrows.mk₀ tetrahedronFoldCompositePath) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  apply CategoryTheory.Functor.ext (fun k => ?_)
  apply Path.ext
  have hm : ULift.up 1 ∈ (P.obj k).I ∪ (Q.obj k).I ∨
      ULift.up 2 ∈ (P.obj k).I ∪ (Q.obj k).I := by
    have hj : j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl
    · exact Or.inl (Or.inl (P.obj k).right)
    · exact Or.inr (Or.inl (P.obj k).right)
  ext l
  change (l.down = 0 ∨ l.down = 3 ∨ l.down = 2 ∧
    (ULift.up 1 ∈ (P.obj k).I ∪ (Q.obj k).I ∨
      ULift.up 2 ∈ (P.obj k).I ∪ (Q.obj k).I)) ↔
    (l.down = 0 ∨ l.down = 3 ∨ l.down = 2)
  simp only [hm, and_true]

/-- 畳み込みは冪等。 -/
lemma tetrahedronPathFold_idempotent :
    tetrahedronPathFold.{u} ⋙ tetrahedronPathFold = tetrahedronPathFold := by
  apply CategoryTheory.Functor.ext (fun P => ?_)
  apply Path.ext
  ext l
  simp [tetrahedronPathFold, tetrahedronPathFoldObj]

/-- 畳み込みで不変な長い native Hom は、二つの内面で全体が一致する。 -/
lemma tetrahedron_nativeLongHom_eq_of_fold
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (t : (SimplicialNerve C) _⦋3⦌)
    (ht : nerveMap tetrahedronPathFold ≫ t.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩ =
      t.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩) :
    ((SimplicialNerve C).δ (1 : Fin 4) t).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩ =
      ((SimplicialNerve C).δ (2 : Fin 4) t).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩ := by
  change nerveMap _ ≫ t.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩ =
    nerveMap _ ≫ t.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩
  conv_lhs => rw [← ht]
  conv_rhs => rw [← ht]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact congrArg (fun F :
    Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2) ⥤
      Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) => nerveMap F)
    tetrahedronPathFold_faces

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
