module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereClosureOperations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleExtensionSphereComparison
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-!
概要：固定 sphere-free 閉包の中に、各代表加群と実同型な一セル代表を指定する。
方針：ordinal 1 の直前区間を一元添字とし、零次 sphere の直和を比較する。
規約：閉包集合を同型飽和へ置換しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ)

/-- κ 内の ordinal 1 のラベル。 -/
def dgKappaOneLabel : κ.ord.ToType :=
  Ordinal.ToType.mk ⟨1, by
    have h : (1 : Cardinal.{u}) < κ := lt_trans (by simp) hκ
    simpa using (Cardinal.ord_lt_ord.mpr h)⟩

/-- 同じラベルの直前区間は一元集合。 -/
@[instance_reducible] def dgKappaOneLabelUnique : Unique (Set.Iio (dgKappaOneLabel hκ)) := by
  have ho : (1 : Ordinal) < κ.ord := by
    have h : (1 : Cardinal.{u}) < κ := lt_trans (by simp) hκ
    simpa using Cardinal.ord_lt_ord.mpr h
  let z : κ.ord.ToType := Ordinal.ToType.mk (o := κ.ord) ⟨0, by
    exact lt_trans (show (0 : Ordinal.{u}) < 1 by simp) ho⟩
  have hz : z < dgKappaOneLabel hκ := by
    change Ordinal.ToType.mk ⟨0, _⟩ < Ordinal.ToType.mk ⟨1, _⟩
    exact (Ordinal.ToType.mk.lt_iff_lt).mpr (by simp)
  refine { default := ⟨z, hz⟩, uniq := ?_ }
  intro i
  apply Subtype.ext
  apply Ordinal.ToType.mk.symm.injective
  apply Subtype.ext
  have hi : (Ordinal.ToType.mk.symm i.val).val < 1 := by
    have hi := (Ordinal.ToType.mk.symm.lt_iff_lt).mpr i.property
    change (Ordinal.ToType.mk.symm i.val).val <
      (Ordinal.ToType.mk.symm (dgKappaOneLabel hκ)).val at hi
    simpa only [dgKappaOneLabel, OrderIso.symm_apply_apply] using hi
  simpa [z] using Order.lt_one_iff.mp hi

/-- 対象 x の零次 sphere 一つからなる、同じ基底族のラベル。 -/
def dgKappaRepresentableSeedIndex (x : D) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ :=
  ⟨dgKappaOneLabel hκ, fun _ => ((equivShrink D) x, 0)⟩

/-- 固定基底の一セル直和代表と、元の代表加群との実 dg 同型。 -/
def dgKappaRepresentableSeedIso (x : D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R D (dgKappaRepresentableSeedIndex D hκ x) ≅
      ForgetEnrichment.of (Complex R) (representable R x) := by
  let U := dgKappaOneLabelUnique hκ
  letI : Unique (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeCells D (dgKappaRepresentableSeedIndex D hκ x)) :=
    { default := ULift.up U.default
      uniq j := by apply ULift.ext; exact U.uniq j.down }
  exact coproductUniqueIso _ ≪≫
    eqToIso (by simp [dgKappaRepresentableSeedIndex]) ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFreeSphereZeroIso R D x

/-- 上の代表は、新 cone の固定 objects 集合にそのまま属する。 -/
lemma dgKappaRepresentableSeed_mem (x : D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R D (dgKappaRepresentableSeedIndex D hκ x)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_sphereFree R D hκ _

/-- 元の全 Hom Yoneda 同型により、代表加群の実同型を元の閉射の同型へ反映する。 -/
def dgRepresentableReflectIso {x y : D}
    (e : ForgetEnrichment.of (Complex R) (representable R x) ≅
      ForgetEnrichment.of (Complex R) (representable R y)) :
    ForgetEnrichment.of (Complex R) x ≅ ForgetEnrichment.of (Complex R) y := by
  have hY : ∀ x y : D, IsIso ((dgYoneda R D).map x y) := by
    intro x y
    change IsIso (dgYonedaIso R x (representable R y)).inv
    infer_instance
  letI := (dgYoneda R D).onClosed_full_of_homIso hY
  letI := (dgYoneda R D).onClosed_faithful_of_homIso hY
  exact (dgYoneda R D).onClosed.preimageIso e

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
