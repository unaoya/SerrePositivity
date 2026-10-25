module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomComplex
/-!
概要：係数 span の実 Hom 複体の単位を、元の閉単位元から構成する。
方針：単位語が span に入ることと微分零から単位複体の射を作り、実埋め込みで照合する。
規約：元の dg 単位の値を保持する。
使われ方：c′ の実 dg 係数閉包の単位鎖写像。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Limits MonoidalCategory
variable {I J : Type u} (source target : I → J) (degree : I → ℤ)
  (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (value : J → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
namespace DGGeneratedHomWord

def homUnitCycle (x : J) : zeroCycles (homComplex source target degree R D value coefficient x x) :=
  ⟨⟨(unitElement R (value x)).val,
    evaluate_mem_span source target degree R D value coefficient (.unit x)⟩, by
      change (homComplex source target degree R D value coefficient x x).d 0 1 _ = 0
      apply Subtype.ext
      change differential R (unitElement R (value x)).val = 0
      exact (unitElement R (value x)).property⟩

def homUnit (x : J) : 𝟙_ (Complex R) ⟶ homComplex source target degree R D value coefficient x x :=
  unitFromCycle _ (homUnitCycle source target degree R D value coefficient x)

lemma homUnit_inclusion (x : J) :
    homUnit source target degree R D value coefficient x ≫
      inclusion source target degree R D value coefficient x x = eId (Complex R) (value x) := by
  apply (unitCycleEquiv _).injective
  change cycleFromUnit _ (_ ≫ _) = unitElement R (value x)
  apply Subtype.ext
  rw [cycleFromUnit_postcomp]
  rw [homUnit, cycleFromUnit_unitFromCycle]
  rfl

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
