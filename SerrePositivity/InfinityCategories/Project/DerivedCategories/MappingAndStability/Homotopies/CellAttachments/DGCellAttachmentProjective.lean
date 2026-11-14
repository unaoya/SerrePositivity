module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.ComplexHomotopies.ComplexProjectiveClosure
public import SerrePositivity.DifferentialGraded.Complexes.TensorShift
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Length

/-!
概要：同じ全境界 cell 付加の Hom の K-projective 性。
方針：path 長の各商の tensor・余積と、全次数分裂する長さ filtration を使う。
規約：追加微分を落とさず、元の attachedHom について証明する。
使われ方：固定 cell source の射影性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded HomologicalComplex MonoidalCategory
open DifferentialGraded.DGCellAttachment
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

omit [Small.{u} I] in
lemma dgCellTerm_isKProjective (hD : ∀ x y : D, (homObject A D x y).IsKProjective)
    (w : List I) (x y : D) : (C.term A D I w x y).IsKProjective := by
  induction w generalizing x y with
  | nil => exact hD x y
  | cons i w ih =>
    let := hD x (C.source i)
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSphere_isKProjective A (C.degree i)
    let := ih (C.target i) y
    let := complexTensor_isKProjective A (C.generator A D I i) (C.term A D I w (C.target i) y)
    exact complexTensor_isKProjective A _ _

lemma dgCellExactLength_isKProjective (hD : ∀ x y : D, (homObject A D x y).IsKProjective)
    (n : ℕ) (x y : D) : (C.exactLengthHom A D I n x y).IsKProjective :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexCoproduct_isKProjective A _ (fun w => dgCellTerm_isKProjective A D I C hD w.val x y)

lemma dgCellLength_isKProjective (hD : ∀ x y : D, (homObject A D x y).IsKProjective)
    (n : ℕ) (x y : D) : (C.lengthHom A D I n x y).IsKProjective := by
  induction n with
  | zero =>
    let := dgCellExactLength_isKProjective A D I C hD 0 x y
    exact CochainComplex.isKProjective_of_iso (asIso (C.lengthQuotient A D I 0 x y)).symm
  | succ n ih =>
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexDegreewiseSplit_isKProjective A (C.lengthShortComplex A D I n x y)
      (C.lengthSplitting A D I n x y) ih
      (dgCellExactLength_isKProjective A D I C hD (n + 1) x y)

lemma dgCellAttachedHom_isKProjective (hD : ∀ x y : D, (homObject A D x y).IsKProjective)
    (x y : D) : (C.attachedHom A D I x y).IsKProjective := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSequentialColimit_isKProjective A (C.lengthDiagram A D I x y)
    (C.lengthCocone A D I x y) (C.lengthIsColimit A D I x y)
    (fun n => dgCellLength_isKProjective A D I C hD n x y)
    (fun n i => (C.lengthSplitting A D I n x y i).r)
  intro n i
  exact (C.lengthSplitting A D I n x y i).f_r

/-- 元 Hom の包含の次数付き左逆。追加微分との可換性は要求しない。 -/
def dgCellOriginalGradedRetraction (x y : D) (i : ℤ) :
    (C.attachedHom A D I x y).X i ⟶ (homObject A D x y).X i :=
  (Sigma.desc (fun w : List I => if h : w = [] then
    eqToHom (by subst w; rfl) else 0) :
      C.internalHom A D I x y ⟶ homObject A D x y).f i

lemma dgCellOriginalGradedRetraction_fac (x y : D) (i : ℤ) :
    (C.originalHomInclusion A D I x y).f i ≫
      dgCellOriginalGradedRetraction A D I C x y i = 𝟙 _ := by
  change (Sigma.ι (fun w : List I => C.term A D I w x y) []).f i ≫
    (Sigma.desc (fun w : List I => if h : w = [] then
      eqToHom (by subst w; rfl) else 0) :
        C.internalHom A D I x y ⟶ homObject A D x y).f i = 𝟙 _
  rw [← HomologicalComplex.comp_f, Sigma.ι_comp_desc]
  simp

end SerrePositivity.InfinityCategories.Project.DerivedCategories
