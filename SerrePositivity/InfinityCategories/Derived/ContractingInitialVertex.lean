module
public import SerrePositivity.InfinityCategories.Derived.DGBoundarySourceExtension
public import SerrePositivity.InfinityCategories.Derived.DGBoundaryOneExtension
public import SerrePositivity.InfinityCategories.Core.Terminal

/-! # 収縮元を持つ dg 対象の始対象性

概要：収縮対象は dg nerve の実際の始対象となる。
方針：固定した最初の頂点を持つ任意の全境界を、明示的な原始元で充填する。
規約：全正次元の境界を扱う。使われ方：β3 の商の指定対象の零化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 収縮元を持つ dg 対象の頂点は、実全境界充填による始対象。 -/
lemma dgNerve_contractingElement_isInitialVertex (x : D) (h : GradedHom A x x (-1))
    (dh : (homObject A D x x).d (-1) 0 h = (unitElement A x).val) :
    IsInitialVertex (X := dgNerve A D) (Simplex.vertex x) := by
  intro n b hb
  cases n with
  | zero => exact dgNerve_boundary_one_extension b
  | succ n =>
    have hx := dgBoundaryZeroData_first_obj b x hb
    have hh : ∃ h' : GradedHom A ((dgBoundaryZeroData b).obj 0)
        ((dgBoundaryZeroData b).obj 0) (-1),
        (homObject A D ((dgBoundaryZeroData b).obj 0) ((dgBoundaryZeroData b).obj 0)).d
          (-1) 0 h' = (unitElement A ((dgBoundaryZeroData b).obj 0)).val := by
      rw [hx]
      exact ⟨h, dh⟩
    obtain ⟨h', dh'⟩ := hh
    exact dgBoundarySourceExtension b h' dh'

end SerrePositivity.InfinityCategories
