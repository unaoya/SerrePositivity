module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ProjectionAdjunctionUnits
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeObject

/-! D 随伴の同じ余単位を元の実閉 gluing 射へ持ち上げる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (X : DGGluingObject R C D M)
local notation "G" => DGGluingObject R C D M
local notation "Q" => toHomotopy R G
local notation "P" => DGFunctor.onHomotopy (dgGluingRight R C D M)
local notation "S" => dgGluingDSectionHomotopy R C D M hC

/-- 右射影の同じ値を D 切断で戻した、実 gluing 対象。 -/
def dgGluingDecompositionDSource : G :=
  ForgetEnrichment.to (Complex R)
    ((S).obj ((P).obj ((Q).obj (ForgetEnrichment.of (Complex R) X)))).as

lemma dgGluingDecompositionDSource_left_zero :
    dgGluingFactorIsZero R C (dgGluingDecompositionDSource R C D M hC X).left :=
  dgGluingDSectionHomotopy_left_zero R C D M hC
    ((P).obj ((Q).obj (ForgetEnrichment.of (Complex R) X)))

/-- 元の商関手の充満性で選ぶ、同じ D 余単位の実閉 gluing 射。 -/
def dgGluingDecompositionArrow :
    ForgetEnrichment.of (Complex R) (dgGluingDecompositionDSource R C D M hC X) ⟶
      ForgetEnrichment.of (Complex R) X :=
  (Q).preimage ((dgGluingDProjectionAdjunction R C D M hC).counit.app
    ((Q).obj (ForgetEnrichment.of (Complex R) X)))

lemma dgGluingDecompositionArrow_map :
    (Q).map (dgGluingDecompositionArrow R C D M hC X) =
      (dgGluingDProjectionAdjunction R C D M hC).counit.app
        ((Q).obj (ForgetEnrichment.of (Complex R) X)) :=
  (Q).map_preimage _

/-- 同じ実閉射の右成分は、元の D の H⁰ で同型。 -/
lemma dgGluingDecompositionArrow_right_isIso :
    IsIso ((toHomotopy R D).map (dgGluingConeRightArrow R C D M
      (dgGluingDecompositionDSource R C D M hC X) X
      (dgGluingDecompositionArrow R C D M hC X))) := by
  let ff := dgGluingDSectionHomotopyFullyFaithful R C D M hC
  let := ff.full
  let := ff.faithful
  change IsIso ((P).map ((Q).map (dgGluingDecompositionArrow R C D M hC X)))
  rw [dgGluingDecompositionArrow_map]
  infer_instance

end SerrePositivity.InfinityCategories
