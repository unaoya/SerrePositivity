module
public import SerrePositivity.KST.SConstruction.RelativeIteratedRows

/-! # 相対加法性の全正有限反復
概要：全ての正の反復 core S• 実現に対し E(A,C,B) の元の二評価が積への弱同値となる。
方針：単回加法性を基底に、行・対角・自然な反復座標比較で帰納する。
規約：零回の core には加法性を主張しない。使われ方：連結 K の相対加法性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.SimplicialModel

/-- 反復座標同型は相対図式の元の二評価の射対と厳密に可換。 -/
lemma iteratedSRealizationCoordinateIso_relativeAdditivity {X : StableModel.{u}} (r : ℕ)
    (A B : ClosedStablePredicate X) :
    relativeIteratedSAdditivityMap r A B ≫
      ((iteratedSRealizationCoordinateIso r (closedStableModel A)).hom ⊗ₘ
        (iteratedSRealizationCoordinateIso r (closedStableModel B)).hom) =
      (iteratedSRealizationCoordinateIso r (relativeCofiberStableModel A B)).hom ≫
        relativeMultiRealizationAdditivityMap (r + 1) A B := by
  rw [relativeIteratedSAdditivityMap_eq]
  change CartesianMonoidalCategory.lift _ _ ≫ (_ ⊗ₘ _) =
    _ ≫ CartesianMonoidalCategory.lift _ _
  rw [CartesianMonoidalCategory.lift_map, CartesianMonoidalCategory.comp_lift,
    iteratedSRealizationCoordinateIso_naturality, iteratedSRealizationCoordinateIso_naturality]

/-- 前段の相対加法性から次の回数の相対加法性が従う。 -/
lemma relativeMultiRealizationAdditivityMap_step_localized_isIso (r : ℕ)
    (hr : ∀ (Y : StableModel.{u}) (P Q : ClosedStablePredicate Y),
      IsIso (AnodyneHomotopy.anodyneQ.map (relativeMultiRealizationAdditivityMap r P Q)))
    {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeMultiRealizationAdditivityMap (r + 1) A B)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := relativeIteratedSAdditivityMap_localized_isIso r hr A B
  have he := congrArg Q.map (iteratedSRealizationCoordinateIso_relativeAdditivity r A B)
  rw [Q.map_comp, Q.map_comp] at he
  have hi : IsIso
      (Q.map (iteratedSRealizationCoordinateIso r (relativeCofiberStableModel A B)).hom ≫
        Q.map (relativeMultiRealizationAdditivityMap (r + 1) A B)) := he ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp hi

/-- 相対 E(A,C,B) の全正有限反復 core S• 実現の加法性。 -/
lemma relativeMultiRealizationAdditivityMap_localized_isIso (r : ℕ)
    {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeMultiRealizationAdditivityMap (r + 1) A B)) := by
  induction r generalizing X with
  | zero => exact relativeMultiRealizationAdditivityMap_one_localized_isIso A B
  | succ r ih =>
    exact relativeMultiRealizationAdditivityMap_step_localized_isIso (r + 1) (fun _ => ih) A B

/-- 正の回数で指定した相対有限反復加法性。 -/
lemma relativeMultiRealizationAdditivityMap_localized_isIso_of_pos (r : ℕ) (hr : 0 < r)
    {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeMultiRealizationAdditivityMap r A B)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  exact relativeMultiRealizationAdditivityMap_localized_isIso r A B

end SerrePositivity.KST.SConstruction
