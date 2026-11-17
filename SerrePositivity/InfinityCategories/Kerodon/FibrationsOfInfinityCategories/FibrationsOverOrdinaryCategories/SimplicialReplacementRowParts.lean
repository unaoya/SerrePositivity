module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowMaps
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
概要：barの一つの行を、基底射列の退化・非退化の部分へ分ける。
方針：内側の係数作用素は基底射列を変えないため、任意の基底部分集合が部分複体となる。
規約：基底の退化と係数の退化を区別する。外側のlatchingとの同定は別に示す。
使われ方：IS-W2 R03f.2の相対latchingの余積表示。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
variable {I : Type u} [SmallCategory I]

/-- 基底射列の任意の部分集合で指定された行の部分複体。 -/
def simplicialReplacementRowPart (F : I ⥤ SSet.{u}) (n : ℕ)
    (P : Set (ComposableArrows I n)) : (simplicialReplacementRow F n).Subcomplex where
  obj _ := {s | s.1 ∈ P}
  map _ := by
    intro s hs
    exact hs

/-- 基底射列が退化である成分の、係数全体を持つ部分複体。 -/
abbrev simplicialReplacementDegenerateRow (F : I ⥤ SSet.{u}) (n : ℕ) :=
  simplicialReplacementRowPart F n ((nerve I).degenerate n)

/-- 基底射列が非退化である成分の、係数全体を持つ部分複体。 -/
abbrev simplicialReplacementNondegenerateRow (F : I ⥤ SSet.{u}) (n : ℕ) :=
  simplicialReplacementRowPart F n ((nerve I).nonDegenerate n)

/-- 同じ二つの基底成分は、元の行をすべて覆う。 -/
theorem simplicialReplacementRowParts_sup (F : I ⥤ SSet.{u}) (n : ℕ) :
    simplicialReplacementDegenerateRow F n ⊔ simplicialReplacementNondegenerateRow F n = ⊤ := by
  classical
  ext q s
  change (s.1 ∈ (nerve I).degenerate n ∨ s.1 ∈ (nerve I).nonDegenerate n) ↔ True
  simp only [SSet.nonDegenerate, Set.mem_compl_iff, or_not, iff_self]

/-- 同じ二つの基底成分の交わりは空である。 -/
theorem simplicialReplacementRowParts_inf (F : I ⥤ SSet.{u}) (n : ℕ) :
    simplicialReplacementDegenerateRow F n ⊓ simplicialReplacementNondegenerateRow F n = ⊥ := by
  ext q s
  change (s.1 ∈ (nerve I).degenerate n ∧ s.1 ∈ (nerve I).nonDegenerate n) ↔ False
  simp only [SSet.nonDegenerate, Set.mem_compl_iff, and_not_self, iff_self]

/-- 元の係数の射は、同じ基底部分の全係数をそのまま保つ。 -/
def simplicialReplacementRowPartMap {F G : I ⥤ SSet.{u}} (η : F ⟶ G) (n : ℕ)
    (P : Set (ComposableArrows I n)) :
    (simplicialReplacementRowPart F n P : SSet.{u}) ⟶ simplicialReplacementRowPart G n P :=
  Subcomplex.lift ((simplicialReplacementRowPart F n P).ι ≫ simplicialReplacementRowMap η n) (by
    rintro q _ ⟨s, rfl⟩
    exact s.property)

/-- 同じ基底部分への制限は、元の包含と厳密に可換する。 -/
theorem simplicialReplacementRowPartMap_inclusion {F G : I ⥤ SSet.{u}} (η : F ⟶ G)
    (n : ℕ) (P : Set (ComposableArrows I n)) :
    simplicialReplacementRowPartMap η n P ≫ (simplicialReplacementRowPart G n P).ι =
      (simplicialReplacementRowPart F n P).ι ≫ simplicialReplacementRowMap η n := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
