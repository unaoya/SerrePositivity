module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.LengthFiltration

/-! # path長filtrationの遷移射と最終Homへの包含 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

def lengthInternalMap (m n : ℕ) (x y : D) :
    C.lengthInternalHom A D I m x y ⟶ C.lengthInternalHom A D I n x y :=
  ComplexCoproduct.select (fun w => C.term A D I w x y) (lengthSet I m) (lengthSet I n)

lemma lengthInternalMap_inclusion (m n : ℕ) (h : m ≤ n) (x y : D) :
    C.lengthInternalMap A D I m n x y ≫ C.lengthInclusion A D I n x y =
      C.lengthInclusion A D I m x y :=
  ComplexCoproduct.select_inclusion _ _ _ (fun _ hw => hw.trans h)

lemma lengthInternalMap_replacement (m n : ℕ) (h : m ≤ n) (x y : D) :
    (Cochain.ofHom (C.lengthInternalMap A D I m n x y)).comp
      (C.lengthReplacement A D I n x y) (zero_add 1) =
    (C.lengthReplacement A D I m x y).comp
      (Cochain.ofHom (C.lengthInternalMap A D I m n x y)) (add_zero 1) := by
  apply cochain_postcomp_injective_of_retraction
    (C.lengthInclusion A D I n x y) (C.lengthProjection A D I n x y)
    (C.lengthInclusion_projection A D I n x y) _ 1
  dsimp only
  rw [Cochain.comp_assoc_of_third_is_zero_cochain, ← lengthReplacement_inclusion,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    lengthInternalMap_inclusion A D I C m n h,
    lengthReplacement_inclusion, Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp, lengthInternalMap_inclusion A D I C m n h]

def lengthMap (m n : ℕ) (h : m ≤ n) (x y : D) :
    C.lengthHom A D I m x y ⟶ C.lengthHom A D I n x y :=
  perturbMap (C.lengthInternalMap A D I m n x y)
    (C.lengthReplacement A D I m x y) (C.lengthReplacement A D I n x y)
    (C.lengthReplacement_closed A D I m x y) (C.lengthReplacement_closed A D I n x y)
    (C.lengthReplacement_square_zero A D I m x y) (C.lengthReplacement_square_zero A D I n x y)
    (C.lengthInternalMap_replacement A D I m n h x y)

lemma lengthMap_f (m n : ℕ) (h : m ≤ n) (x y : D) (i : ℤ) :
    (C.lengthMap A D I m n h x y).f i = (C.lengthInternalMap A D I m n x y).f i := rfl

lemma lengthMap_inclusion (m n : ℕ) (h : m ≤ n) (x y : D) :
    C.lengthMap A D I m n h x y ≫ C.lengthHomInclusion A D I n x y =
      C.lengthHomInclusion A D I m x y := by
  apply HomologicalComplex.Hom.ext
  funext i
  change (C.lengthInternalMap A D I m n x y).f i ≫
    (C.lengthInclusion A D I n x y).f i = (C.lengthInclusion A D I m x y).f i
  exact congrArg (fun f => f.f i) (C.lengthInternalMap_inclusion A D I m n h x y)

lemma lengthMap_self (n : ℕ) (x y : D) :
    C.lengthMap A D I n n le_rfl x y = 𝟙 _ := by
  apply (cancel_mono (C.lengthHomInclusion A D I n x y)).1
  rw [lengthMap_inclusion, Category.id_comp]

lemma lengthMap_comp (l m n : ℕ) (hlm : l ≤ m) (hmn : m ≤ n) (x y : D) :
    C.lengthMap A D I l m hlm x y ≫ C.lengthMap A D I m n hmn x y =
      C.lengthMap A D I l n (hlm.trans hmn) x y := by
  apply (cancel_mono (C.lengthHomInclusion A D I n x y)).1
  rw [Category.assoc, lengthMap_inclusion, lengthMap_inclusion, lengthMap_inclusion]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
