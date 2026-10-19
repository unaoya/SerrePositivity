module
public import SerrePositivity.InfinityCategories.Derived.DGClosedZeroVertex
public import SerrePositivity.DifferentialGraded.Module.Zero

/-! # dg 加群圏の nerve の実零対象

概要：全 Hom end を持つ dg 加群圏の nerve に具体的な零頂点を供給する。
方針：閉零圏の零加群の恒等射の消滅を実全境界充填へ接続する。
規約：加群の準同型による局所化はまだ行わない。使われ方：β3 の ambient dg 加群圏。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全 Hom end を持つ右 dg 加群圏の dg nerve。 -/
abbrev dgModuleNerve := dgNerve A (RightModule A D)

/-- dg 加群の nerve の具体的な零頂点。 -/
def dgModuleNerveZeroVertex : (dgModuleNerve A D).obj (Opposite.op (SimplexCategory.mk 0)) :=
  Simplex.vertex (zeroModule A D)

/-- 具体的な零加群は nerve の実際の始対象かつ終対象。 -/
lemma dgModuleNerveZeroVertex_isZero :
    IsZeroVertex (X := dgModuleNerve A D) (dgModuleNerveZeroVertex A D) :=
  dgNerve_isZeroVertex_of_closed_isZero (zeroModule A D) (moduleZero_isZero A D)

/-- 全 dg 加群圏の nerve は零対象を持つ。 -/
instance dgModuleNerve_hasZeroVertex : HasZeroVertex (dgModuleNerve A D) where
  exists_zero := ⟨dgModuleNerveZeroVertex A D, dgModuleNerveZeroVertex_isZero A D⟩

/-- 全対象で零複体である dg 加群は nerve で実際に零対象。 -/
lemma dgModuleNerve_isZeroVertex_of_objectwise_zero (M : RightModule A D)
    (hM : ∀ x : D, IsZero (M.obj (Opposite.op x))) :
    IsZeroVertex (X := dgModuleNerve A D) (Simplex.vertex M) :=
  dgNerve_isZeroVertex_of_closed_isZero M ((module_isZero_iff A D
    (ForgetEnrichment.of (Complex A) M)).2 hM)

end SerrePositivity.InfinityCategories
