module
public import SerrePositivity.InfinityCategories.Derived.ContractingInitialVertex
public import SerrePositivity.InfinityCategories.Derived.ContractingTerminalVertex
public import SerrePositivity.InfinityCategories.Core.Pointed

/-! # 収縮元を持つ dg 対象の零対象性

概要：次数 −1 の収縮元を持つ対象は dg nerve の零対象。
方針：実境界充填による始対象性と写像空間による終対象性を合わせる。
規約：通常の h の零性だけを使わない。使われ方：β3 の商による零化。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 収縮元を持つ対象は dg nerve の零頂点。 -/
lemma dgNerve_contractingElement_isZeroVertex (x : D) (h : GradedHom A x x (-1))
    (dh : (homObject A D x x).d (-1) 0 h = (unitElement A x).val) :
    IsZeroVertex (X := dgNerve A D) (Simplex.vertex x) :=
  ⟨dgNerve_contractingElement_isInitialVertex x h dh,
    dgNerve_contractingElement_isTerminalVertex x h dh⟩

/-- 収縮元付き対象を選ばれた零頂点としてまとめる。 -/
def dgNerveContractingZeroVertex (x : D) (h : GradedHom A x x (-1))
    (dh : (homObject A D x x).d (-1) 0 h = (unitElement A x).val) :
    ZeroVertex (dgNerve A D) :=
  ⟨Simplex.vertex x, dgNerve_contractingElement_isInitialVertex x h dh,
    dgNerve_contractingElement_isTerminalVertex x h dh⟩

end SerrePositivity.InfinityCategories
