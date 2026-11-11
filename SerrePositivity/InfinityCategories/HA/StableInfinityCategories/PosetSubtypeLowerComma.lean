module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeExtensions

/-!
概要：順序部分型の左 comma と同じ下方添字の nerve を同定する。
方針：元の射影・実余錐・全単体の頂点式を保持して比較する。
規約：一般安定性の結論は先取りしない。使われ方：HA 1.4.2.15 の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P : Type u} [PartialOrder P]

abbrev PosetSubtypeLowerIndex {P : Type u} [PartialOrder P] (T : P → Prop) (c : P) :=
  {p : P // T p ∧ p ≤ c}

def posetSubtypeCommaToLower {P : Type u} [PartialOrder P] (T : P → Prop) (c : P) :
    CostructuredArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T) c ⥤ PosetSubtypeLowerIndex T c where
  obj a := ⟨a.left.val, a.left.property, leOfHom a.hom⟩
  map f := homOfLE (leOfHom f.left)

def posetSubtypeLowerToComma {P : Type u} [PartialOrder P] (T : P → Prop) (c : P) :
    PosetSubtypeLowerIndex T c ⥤ CostructuredArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T) c where
  obj p :=
    { left := ⟨p.val, p.property.1⟩
      right := ⟨⟨⟩⟩
      hom := by
        change p.val ⟶ c
        exact homOfLE p.property.2 }
  map f := CostructuredArrow.homMk (homOfLE (leOfHom f)) (by apply Subsingleton.elim)

def posetSubtypeCommaLowerNerveIso {P : Type u} [PartialOrder P] (T : P → Prop) (c : P) :
    nerve (CostructuredArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T) c) ≅
      nerve (PosetSubtypeLowerIndex T c) where
  hom := nerveMap (posetSubtypeCommaToLower T c)
  inv := nerveMap (posetSubtypeLowerToComma T c)
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    change (s ⋙ posetSubtypeCommaToLower T c) ⋙ posetSubtypeLowerToComma T c = s
    apply CategoryTheory.Functor.ext
    · intro i j f
      apply CostructuredArrow.ext
      apply Subsingleton.elim
    · intro i
      apply CostructuredArrow.obj_ext _ _ (Subtype.ext rfl)
      apply Subsingleton.elim
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    change (s ⋙ posetSubtypeLowerToComma T c) ⋙ posetSubtypeCommaToLower T c = s
    apply CategoryTheory.Functor.ext
    · intro i j f
      apply Subsingleton.elim
    · intro i
      apply Subtype.ext
      rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
