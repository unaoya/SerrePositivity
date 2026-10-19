module
public import SerrePositivity.InfinityCategories.Derived.DGBoundaryAssembly
public import SerrePositivity.InfinityCategories.Derived.ContractingElementHomBoundaries
public import SerrePositivity.InfinityCategories.DGNerve.ReplacementLocality

/-! # dg nerve 全境界の最上位成分の収縮による解

概要：始点が収縮する単体データの最上位の方程式を、明示的な原始元で解く。
方針：真部分集合の方程式から右辺の閉性を得て、最上位だけを置換する。
規約：面の成分と全既知方程式は保持する。使われ方：β3 の始対象性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 収縮する最初の対象に基づく最上位の射族。 -/
def dgBoundarySourceTopHom {n : ℕ} (s : SimplexData A D (n + 2))
    (h : GradedHom A (s.obj 0) (s.obj 0) (-1)) :
    ∀ a b k (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 3))).card),
      a = Finset.univ.min' (Index.nonempty hI) →
      b = Finset.univ.max' (Index.nonempty hI) →
      k = 2 - ((Finset.univ : Finset (Fin (n + 3))).card : ℤ) →
      GradedHom A (s.obj a) (s.obj b) k := by
  intro a b k hI ha hb hk
  have ha0 : a = 0 := ha.trans (HornData.univ_min_zero n _).symm
  cases ha0
  exact contractingSourcePrimitive h k (s.rhs Finset.univ 0 b k hI ha hb hk)

/-- 真部分集合が方程式を満たすとき、最上位の原始元の微分はその右辺。 -/
lemma dgBoundarySourceTopHom_differential {n : ℕ} (s : SimplexData A D (n + 2))
    (he : ∀ I, I ≠ Finset.univ → s.Equation I)
    (h : GradedHom A (s.obj 0) (s.obj 0) (-1))
    (dh : (homObject A D (s.obj 0) (s.obj 0)).d (-1) 0 h = (unitElement A (s.obj 0)).val)
    (a b : Fin (n + 3)) (k : ℤ) (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 3))).card)
    (ha : a = Finset.univ.min' (Index.nonempty hI))
    (hb : b = Finset.univ.max' (Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 3))).card : ℤ)) :
    differential A (dgBoundarySourceTopHom s h a b k hI ha hb hk) =
      s.rhs Finset.univ a b k hI ha hb hk := by
  have ha0 : a = 0 := ha.trans (HornData.univ_min_zero n _).symm
  cases ha0
  change differential A (contractingSourcePrimitive h k _) = _
  apply contractingSourcePrimitive_differential h dh
  apply s.differential_rhs_zero_of_proper_equations
  intro J hJ
  exact he J ((Finset.ssubset_iff_subset_ne.mp hJ).2)

/-- 収縮元の原始元を最上位に挿入した単体データ。 -/
def dgBoundarySourceFillerData {n : ℕ} (s : SimplexData A D (n + 2))
    (h : GradedHom A (s.obj 0) (s.obj 0) (-1)) : SimplexData A D (n + 2) :=
  s.replace Finset.univ (dgBoundarySourceTopHom s h)

/-- 最上位の原始元の挿入後は全ての方程式が成り立つ。 -/
lemma dgBoundarySourceFillerData_equation {n : ℕ} (s : SimplexData A D (n + 2))
    (he : ∀ I, I ≠ Finset.univ → s.Equation I)
    (h : GradedHom A (s.obj 0) (s.obj 0) (-1))
    (dh : (homObject A D (s.obj 0) (s.obj 0)).d (-1) 0 h = (unitElement A (s.obj 0)).val)
    (I : Finset (Fin (n + 3))) : (dgBoundarySourceFillerData s h).Equation I := by
  by_cases hfull : I = Finset.univ
  · subst I
    intro a b k hI ha hb hk
    rw [dgBoundarySourceFillerData, SimplexData.replace_hom_same, SimplexData.rhs_replace_self]
    exact dgBoundarySourceTopHom_differential s he h dh a b k hI ha hb hk
  · exact s.equation_replace_of_not_subset _ _ I
      (fun hn => hfull (le_antisymm (Finset.subset_univ I) hn)) (he I hfull)

/-- 最上位の挿入は全ての面を厳密に保つ。 -/
lemma dgBoundarySourceFillerData_pullback_face {n : ℕ} (s : SimplexData A D (n + 2))
    (h : GradedHom A (s.obj 0) (s.obj 0) (-1)) (j : Fin (n + 3)) :
    (dgBoundarySourceFillerData s h).pullback j.succAboveOrderEmb.toOrderHom =
      s.pullback j.succAboveOrderEmb.toOrderHom :=
  s.replace_pullback_of_omits _ _ _ j (Finset.mem_univ j) (Fin.succAbove_ne j)

/-- 始点の収縮から作る、全方程式を持つ実際の dg nerve 単体。 -/
def dgBoundarySourceFiller {n : ℕ} (s : SimplexData A D (n + 2))
    (he : ∀ I, I ≠ Finset.univ → s.Equation I)
    (h : GradedHom A (s.obj 0) (s.obj 0) (-1))
    (dh : (homObject A D (s.obj 0) (s.obj 0)).d (-1) 0 h = (unitElement A (s.obj 0)).val) :
    Simplex A D (n + 2) where
  toSimplexData := dgBoundarySourceFillerData s h
  equation I := dgBoundarySourceFillerData_equation s he h dh I

end SerrePositivity.InfinityCategories
