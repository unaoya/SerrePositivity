module


public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Types.Monomorphisms

/-!
概要：射の逆像で保たれる Type 値の部分図式の余極限からの包含は単射。
方針：部分図式内の代表を some、外の代表を none に送る余錐を作り、余極限で分離する。
規約：図式の全ての射で部分集合の所属を保存・反映することを使う。
使われ方：Goerss–Jardine VIII §1。骨格に制限した latching 図式の単射性。
-/

@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits ConcreteCategory
namespace SerrePositivity.KST.Spectra.CartesianSubfunctorColimit
end SerrePositivity.KST.Spectra.CartesianSubfunctorColimit
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.CartesianSubfunctorColimit
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {J : Type v} [SmallCategory J] [HasColimitsOfShape J (Type u)]
  {F : J ⥤ Type u} (A : Subfunctor F)
  (hA : ∀ {i j : J} (f : i ⟶ j) (x : F.obj i), F.map f x ∈ A.obj j ↔ x ∈ A.obj i)

/-- 部分図式内の代表だけを Option の some に送る余錐。 -/
def splitCocone : Cocone F := by
  classical
  exact {
    pt := Option (colimit A.toFunctor)
    ι := {
      app i := ↾fun x ↦ if hx : x ∈ A.obj i then
        some (colimit.ι A.toFunctor i ⟨x, hx⟩) else none
      naturality i j f := by
        ext x
        change (if hx : F.map f x ∈ A.obj j then
          some (colimit.ι A.toFunctor j ⟨F.map f x, hx⟩) else none) =
          if hx : x ∈ A.obj i then some (colimit.ι A.toFunctor i ⟨x, hx⟩) else none
        by_cases hx : x ∈ A.obj i
        · have hfx := (hA f x).2 hx
          rw [dite_eq_left hfx, dite_eq_left hx]
          apply congrArg some
          exact colimit.w_apply A.toFunctor f ⟨x, hx⟩
        · have hfx : F.map f x ∉ A.obj j := fun h ↦ hx ((hA f x).1 h)
          rw [dite_eq_right hfx, dite_eq_right hx] } }

/-- 代表を分離する余錐の余極限への降下。 -/
def split : colimit F ⟶ Option (colimit A.toFunctor) :=
  colimit.desc F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.splitCocone A hA)

/-- 部分図式の代表には、元の余極限の類を some として返す。 -/
lemma split_ι (i : J) (x : A.toFunctor.obj i) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.split A hA (colimit.ι F i x.val) = some (colimit.ι A.toFunctor i x) := by
  classical
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.split]
  erw [colimit.ι_desc_apply]
  change (if hx : x.val ∈ A.obj i then
    some (colimit.ι A.toFunctor i ⟨x.val, hx⟩) else none) = _
  rw [dite_eq_left x.property]
  rfl

/-- 部分図式の余極限の包含の後では、分離射は some そのもの。 -/
lemma split_map (x : colimit A.toFunctor) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.split A hA (colim.map A.ι x) = some x := by
  obtain ⟨i, y, rfl⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit A.toFunctor) x
  erw [colimit.ι_map_apply]
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.split_ι A hA i y

include hA in
/-- 全ての射で所属を反映する部分図式では、余極限の包含は単射。 -/
lemma mono : Mono (colim.map A.ι) := by
  apply (mono_iff_injective _).mpr
  intro x y h
  have he := congrArg (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.split A hA) h
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.split_map, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.split_map] at he
  exact Option.some.inj he

end
end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
