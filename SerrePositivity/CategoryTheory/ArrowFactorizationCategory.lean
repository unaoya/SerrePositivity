module

public import SerrePositivity.CategoryTheory.AnchoredChain
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-! # The category of actual factorizations of a fixed arrow

Morphisms commute with both external legs. The identity factorizations
at the source and target are initial and terminal, respectively.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.ArrowFactorization
variable {D : Type u} [Category.{v} D] {Y V : D} {g : Y ⟶ V}

structure Hom (a b : ArrowFactorization g) where
  hom : a.middle ⟶ b.middle
  left_comm : a.left ≫ hom = b.left
  right_comm : hom ≫ b.right = a.right

@[ext]
lemma Hom.ext {a b : ArrowFactorization g} {f h : Hom a b} (e : f.hom = h.hom) : f = h := by
  cases f
  cases h
  cases e
  rfl

instance : Category.{v} (ArrowFactorization g) where
  Hom := Hom
  id a := ⟨𝟙 a.middle, by simp, by simp⟩
  comp f h := ⟨f.hom ≫ h.hom, by rw [← Category.assoc, f.left_comm, h.left_comm],
    by rw [Category.assoc, h.right_comm, f.right_comm]⟩
  id_comp f := Hom.ext (Category.id_comp f.hom)
  comp_id f := Hom.ext (Category.comp_id f.hom)
  assoc f h k := Hom.ext (Category.assoc f.hom h.hom k.hom)

@[reassoc (attr := simp)]
lemma left_comp {a b : ArrowFactorization g} (f : a ⟶ b) : a.left ≫ f.hom = b.left := f.left_comm

@[reassoc (attr := simp)]
lemma comp_right {a b : ArrowFactorization g} (f : a ⟶ b) :
    f.hom ≫ b.right = a.right := f.right_comm

@[simp]
lemma id_hom (a : ArrowFactorization g) : (𝟙 a : a ⟶ a).hom = 𝟙 a.middle := rfl

@[simp]
lemma comp_hom {a b c : ArrowFactorization g} (f : a ⟶ b) (h : b ⟶ c) :
    (f ≫ h).hom = f.hom ≫ h.hom := rfl

@[simp]
lemma eqToHom_hom {a b : ArrowFactorization g} (h : a = b) :
    (eqToHom h).hom = eqToHom (congrArg ArrowFactorization.middle h) := by cases h; rfl

lemma eta (a : ArrowFactorization g) :
    ArrowFactorization.mk a.middle a.left a.right a.fac = a := by cases a; rfl

variable (g)

def forget : ArrowFactorization g ⥤ D where
  obj a := a.middle
  map f := f.hom

def source : ArrowFactorization g := ⟨Y, 𝟙 Y, g, by simp⟩
def target : ArrowFactorization g := ⟨V, g, 𝟙 V, by simp⟩

def fromSource (a : ArrowFactorization g) : source g ⟶ a :=
  ⟨a.left, by simp [source], a.fac⟩

def toTarget (a : ArrowFactorization g) : a ⟶ target g :=
  ⟨a.right, a.fac, by simp [target]⟩

def source_isInitial : IsInitial (source g) :=
  IsInitial.ofUniqueHom (fromSource g) (fun a f => Hom.ext (by
    change f.hom = a.left
    simpa only [source, Category.id_comp] using f.left_comm))

def target_isTerminal : IsTerminal (target g) :=
  IsTerminal.ofUniqueHom (toTarget g) (fun a f => Hom.ext (by
    change f.hom = a.right
    simpa only [target, Category.comp_id] using f.right_comm))

def fromSourceNatTrans : (Functor.const (ArrowFactorization g)).obj (source g) ⟶ 𝟭 _ where
  app := fromSource g
  naturality {_ _} _ := (source_isInitial g).hom_ext _ _

def toTargetNatTrans : 𝟭 (ArrowFactorization g) ⟶ (Functor.const _).obj (target g) where
  app := toTarget g
  naturality {_ _} _ := (target_isTerminal g).hom_ext _ _

end SerrePositivity.ArrowFactorization
