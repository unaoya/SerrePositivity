module
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomologyNaturality
/-!
概要：代表加群からの実閉射を、対象での零 cycle と線形に同定する。
方針：全次数 Yoneda 同型を単位複体からの射に適用する。
規約：導来圏やホモトピー商を通さず、閉射そのものと後合成を保持する。
使われ方：c′ の自由代表から余積への閉射の有限係数表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

def representableClosedCycleEquiv (x : D) (M : ModuleCategory R D) :
    (ForgetEnrichment.of (Complex R) (representable R x) ⟶ M) ≃
      zeroCycles ((ForgetEnrichment.to (Complex R) M).obj (op x)) where
  toFun f := cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f ≫
    (dgYonedaIso R x (ForgetEnrichment.to (Complex R) M)).hom)
  invFun z := ForgetEnrichment.homOf (Complex R) (unitFromCycle _ z ≫
    (dgYonedaIso R x (ForgetEnrichment.to (Complex R) M)).inv)
  left_inv f := by
    change unitFromCycle _ (cycleFromUnit _ _) ≫ _ = ForgetEnrichment.homTo (Complex R) f
    rw [unitFromCycle_cycleFromUnit, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv z := by
    change cycleFromUnit _ ((unitFromCycle _ z ≫ _) ≫ _) = z
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, cycleFromUnit_unitFromCycle]

def representableClosedCycleLinearEquiv (x : D) (M : ModuleCategory R D) :
    (ForgetEnrichment.of (Complex R) (representable R x) ⟶ M) ≃ₗ[R]
      zeroCycles ((ForgetEnrichment.to (Complex R) M).obj (op x)) where
  toEquiv := representableClosedCycleEquiv R D x M
  map_add' f g := by
    apply Subtype.ext
    change (dgYonedaIso R x (ForgetEnrichment.to (Complex R) M)).hom.f 0
      ((cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val +
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) g)).val) = _
    exact map_add _ _ _
  map_smul' r f := by
    apply Subtype.ext
    change (dgYonedaIso R x (ForgetEnrichment.to (Complex R) M)).hom.f 0
      (r • (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val) = _
    exact map_smul _ _ _

lemma representableClosedCycleEquiv_postcompose (x : D) {M N : ModuleCategory R D}
    (f : ForgetEnrichment.of (Complex R) (representable R x) ⟶ M) (g : M ⟶ N) :
    (representableClosedCycleEquiv R D x N (f ≫ g)).val =
      ((moduleEvaluation R D x).map g).f 0
        (representableClosedCycleEquiv R D x M f).val := by
  change (dgYonedaIso R x (ForgetEnrichment.to (Complex R) N)).hom.f 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (f ≫ g))).val = _
  rw [← moduleHomCycle_postcompose R D f g]
  exact congrArg (fun k => k.f 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val)
    (dgYonedaIso_postcompose R D x g)

end SerrePositivity.DifferentialGraded
