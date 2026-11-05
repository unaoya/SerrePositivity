module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetArrowCompositionInputs
public import SerrePositivity.InfinityCategories.F1B.Fibrations.TrivialFibrationHomotopy
/-!
概要：指定元二三角形と係数側標準二三角形を、同じ元 Hom 入力上で結ぶ。
方針：実入力 fiber の自明 Kan 射影へ同じ元入力の二持ち上げを渡す。
規約：全 path の一致は相対二次元比較で別途接続する。
使われ方：元入力付き指定対角境界の二辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet
open KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetFirstInputHomotopy_exists :
    ∃ H : SSet.Homotopy (dgGluingHomTargetArrowFirstInputLift R C D E p q X Y)
        (complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y) ≫
          dgGluingHomTargetFirstInputSection R C D E p q X Y),
      H.h ≫ dgGluingHomTargetFirstInputProjection R C D E p q X Y =
        fst _ (Δ[1] : SSet.{max (u + 1) v}) ≫
          complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y) := by
  let := dgGluingHomTargetFirstInputProjection_trivialKanFibration R C D E p q X Y
  obtain ⟨H, hh⟩ := exists_homotopy_over_trivialKanFibration
    (dgGluingHomTargetFirstInputProjection R C D E p q X Y)
    (dgGluingHomTargetArrowFirstInputLift R C D E p q X Y)
    (complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y) ≫
      dgGluingHomTargetFirstInputSection R C D E p q X Y) (by
        rw [dgGluingHomTargetArrowFirstInputLift_input R C D E p q X Y,
          Category.assoc, dgGluingHomTargetFirstInputSection_input R C D E p q X Y,
          Category.comp_id])
  refine ⟨H, ?_⟩
  simpa only [Category.assoc, dgGluingHomTargetFirstInputSection_input R C D E p q X Y,
    Category.comp_id] using hh

def dgGluingHomTargetFirstInputHomotopy :=
  (dgGluingHomTargetFirstInputHomotopy_exists R C D E p q X Y).choose

lemma dgGluingHomTargetFirstInputHomotopy_over :
    (dgGluingHomTargetFirstInputHomotopy R C D E p q X Y).h ≫
      dgGluingHomTargetFirstInputProjection R C D E p q X Y =
    fst _ (Δ[1] : SSet.{max (u + 1) v}) ≫
      complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y) :=
  (dgGluingHomTargetFirstInputHomotopy_exists R C D E p q X Y).choose_spec

lemma dgGluingHomTargetLastInputHomotopy_exists :
    ∃ H : SSet.Homotopy (dgGluingHomTargetArrowLastInputLift R C D E p q X Y)
        (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y) ≫
          dgGluingHomTargetLastInputSection R C D E p q X Y),
      H.h ≫ dgGluingHomTargetLastInputProjection R C D E p q X Y =
        fst _ (Δ[1] : SSet.{max (u + 1) v}) ≫
          complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y) := by
  let := dgGluingHomTargetLastInputProjection_trivialKanFibration R C D E p q X Y
  obtain ⟨H, hh⟩ := exists_homotopy_over_trivialKanFibration
    (dgGluingHomTargetLastInputProjection R C D E p q X Y)
    (dgGluingHomTargetArrowLastInputLift R C D E p q X Y)
    (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y) ≫
      dgGluingHomTargetLastInputSection R C D E p q X Y) (by
        rw [dgGluingHomTargetArrowLastInputLift_input R C D E p q X Y,
          Category.assoc, dgGluingHomTargetLastInputSection_input R C D E p q X Y,
          Category.comp_id])
  refine ⟨H, ?_⟩
  simpa only [Category.assoc, dgGluingHomTargetLastInputSection_input R C D E p q X Y,
    Category.comp_id] using hh

def dgGluingHomTargetLastInputHomotopy :=
  (dgGluingHomTargetLastInputHomotopy_exists R C D E p q X Y).choose

lemma dgGluingHomTargetLastInputHomotopy_over :
    (dgGluingHomTargetLastInputHomotopy R C D E p q X Y).h ≫
      dgGluingHomTargetLastInputProjection R C D E p q X Y =
    fst _ (Δ[1] : SSet.{max (u + 1) v}) ≫
      complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y) :=
  (dgGluingHomTargetLastInputHomotopy_exists R C D E p q X Y).choose_spec

end SerrePositivity.InfinityCategories
