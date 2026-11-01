module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.Word
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Basic

/-!
# 元の列の有限集合による部分語と交わり

概要：二つの語の包含の列の像の交わりを、同じ元の向きを保つ部分語で表す。
方針：列の有限集合の増加列挙を用いる。
規約：空集合も含み、元の全順序と全列の向きを保持する。
使われ方：Dwyer–Kan §4.4 の包含の交わりと graph 図式の proper 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

/-- 元の列の有限集合を、順序と向きを保って列挙した部分語。 -/
def subword (c : Word) (s : Finset (Fin c.length)) : Word :=
  ⟨s.card, fun i => c.direction (s.orderEmbOfFin rfl i)⟩

def subwordInclusion (c : Word) (s : Finset (Fin c.length)) : subword c s ⟶ c where
  orderHom := (s.orderEmbOfFin rfl).toOrderHom
  direction_eq _ := rfl

lemma subwordInclusion_injective (c : Word) (s : Finset (Fin c.length)) :
    Function.Injective (subwordInclusion c s).orderHom := (s.orderEmbOfFin rfl).injective

lemma subwordInclusion_range (c : Word) (s : Finset (Fin c.length)) :
    Set.range (subwordInclusion c s).orderHom = (s : Set (Fin c.length)) :=
  Finset.range_orderEmbOfFin s rfl

/-- 元の語の射の列の像を表す有限集合。 -/
def columnImage {a c : Word} (f : a ⟶ c) : Finset (Fin c.length) :=
  Finset.univ.image f.orderHom

lemma coe_columnImage {a c : Word} (f : a ⟶ c) :
    (columnImage f : Set (Fin c.length)) = Set.range f.orderHom := by
  ext j
  simp only [columnImage, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and,
    Set.mem_range]

/-- 二つの包含の列の像の交わりの部分語。 -/
def intersection {a b c : Word} (f : a ⟶ c) (g : b ⟶ c) : Word :=
  subword c (columnImage f ∩ columnImage g)

def intersectionInclusion {a b c : Word} (f : a ⟶ c) (g : b ⟶ c) : intersection f g ⟶ c :=
  subwordInclusion c (columnImage f ∩ columnImage g)

lemma intersectionInclusion_injective {a b c : Word} (f : a ⟶ c) (g : b ⟶ c) :
    Function.Injective (intersectionInclusion f g).orderHom :=
  subwordInclusion_injective c _

/-- 元の列の交わりは、同じ包含の列の集合として厳密に回収する。 -/
lemma intersectionInclusion_range {a b c : Word} (f : a ⟶ c) (g : b ⟶ c) :
    Set.range (intersectionInclusion f g).orderHom = Set.range f.orderHom ∩ Set.range g.orderHom :=
  by
    change Set.range (subwordInclusion c (columnImage f ∩ columnImage g)).orderHom = _
    rw [subwordInclusion_range, Finset.coe_inter, coe_columnImage, coe_columnImage]

end SerrePositivity.EInfinity.Hammock.Word
