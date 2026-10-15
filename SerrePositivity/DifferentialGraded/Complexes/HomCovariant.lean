module
public import SerrePositivity.DifferentialGraded.Module.LeftRepresentable
public import SerrePositivity.DifferentialGraded.Complexes.ClosedMaps

/-! # 固定始域からの共変Hom dg関手 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- Ch(A)の左representableを使う共変Hom関手。 -/
def homCovariantDG (P : Complex A) : DGFunctor A (Complex A) (Complex A) :=
  leftRepresentable A P

/-- 共変Homの作用は通常順の後合成であり、追加のKoszul符号は付かない。 -/
lemma homCovariantDG_map_element (P T T' : Complex A) (p q n : ℤ) (hn : q + p = n)
    (f : Homogeneous T T' p) (g : Homogeneous P T q) :
    (((homCovariantDG A P).map T T').f p f).v q n hn g = g.comp f hn := by
  change leftAction A (leftRepresentable A P) f g hn = _
  rw [leftRepresentable_action]
  change (p * q).negOnePow • forward A (D := Complex A) g f hn = _
  change (p * q).negOnePow • (enrichedComposition P T T').f n
    (HomologicalComplex.ιTensorObj (homComplex A P T) (homComplex A T T') q p n hn
      (g ⊗ₜ[A] f)) = _
  rw [enrichedComposition_apply, smul_smul, mul_comm q p, Int.units_mul_self, one_smul]

lemma homCovariantDG_closedMap (P : Complex A) {T T' : Complex A} (f : T ⟶ T') :
    closedMap A f ≫ (homCovariantDG A P).map T T' = closedMap A (homPostcompose P f) := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (cycleFromUnit _ (closedMap A f ≫ (homCovariantDG A P).map T T')).val =
    (cycleFromUnit _ (closedMap A (homPostcompose P f))).val
  rw [cycleFromUnit_postcomp, closedMap_cycle, closedMap_cycle]
  apply Cochain.ext₀
  intro r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  change (((homCovariantDG A P).map T T').f 0 (Cochain.ofHom f)).v r r (add_zero r) g =
    (homPostcompose P f).f r g
  rw [homCovariantDG_map_element]
  rfl

end SerrePositivity.DifferentialGraded
