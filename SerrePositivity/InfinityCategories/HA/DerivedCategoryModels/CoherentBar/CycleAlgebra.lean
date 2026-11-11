module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.EndRebaseAlgebra
public import SerrePositivity.DifferentialGraded.Category.Basic
/-!
概要：加群射の閉零 Hom 要素への移送は加法と合成を保つ。
方針：既存の閉 Hom 同値と評価 cochain の合成公式を直接使う。
規約：元の加群射と全 Hom end を保持し、ホモトピー類への移行を行わない。
使われ方：有限正規化の実射と graded 作用素の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgCoherentBarCycle_add {M N : ModuleCategory R D} (f g : M ⟶ N) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (f + g))).val =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val +
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) g)).val :=
  congrArg Subtype.val (closedHomEquiv_add R (RightModule R D) M N f g)

lemma dgCoherentBarCycle_comp {L M N : ModuleCategory R D} (f : L ⟶ M) (g : M ⟶ N) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (f ≫ g))).val =
      compose R (x := ForgetEnrichment.to (Complex R) L)
        (y := ForgetEnrichment.to (Complex R) M) (z := ForgetEnrichment.to (Complex R) N)
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) g)).val
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val
        (show (0 : ℤ) + 0 = 0 from rfl) := by
  apply moduleHomElement_ext R D
    (M := ForgetEnrichment.to (Complex R) L) (N := ForgetEnrichment.to (Complex R) N)
  intro x
  rw [moduleHomCompose_π R D,
    ← moduleEvaluation_cochain R D x (f ≫ g),
    ← moduleEvaluation_cochain R D x f, ← moduleEvaluation_cochain R D x g,
    Functor.map_comp, Cochain.ofHom_comp]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
