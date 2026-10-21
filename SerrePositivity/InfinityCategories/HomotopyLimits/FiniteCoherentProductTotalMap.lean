module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpaceTensorProductTotalMap
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteCommonFiberProductUniversal

/-!
概要：有限 coherent 積の元の小さい全空間から、元の有限共通 fiber 積への比較。
方針：元の二項積の全空間射影を反復し、元の全成分から普遍射を構成する。
規約：元の全空間・底射影・各成分を保持。比較の同値性は別工程。
使われ方：有限 sifted 積比較を元の coherent 余極限頂点へ移すための指定射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の n+1 個の coherent 空間値図式の点ごとの反復積。 -/
def finiteCoherentSpaceProduct {B : SSet.{u + 1}} : (n : ℕ) →
    (Fin (n + 1) → (B ⟶ SpaceInfinity.{u})) → (B ⟶ SpaceInfinity.{u})
  | 0, F => F 0
  | n + 1, F => coherentSpaceTensorProduct (F 0)
      (finiteCoherentSpaceProduct n (fun i ↦ F i.succ))

/-- 元の二項射影の全空間作用を反復した、元の各図式への全空間射影。 -/
def finiteCoherentSpaceProductTotalProjection {B : SSet.{u}} : (n : ℕ) →
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})) →
    (i : Fin (n + 1)) → (smallLeftUnstraightening (finiteCoherentSpaceProduct n F) ⟶
      smallLeftUnstraightening (F i))
  | 0, F, i => eqToHom
      (congrArg (fun j ↦ smallLeftUnstraightening (F j)) (Fin.eq_zero i).symm)
  | n + 1, F, i => Fin.cases
      (coherentSpaceTensorProductTotalFst (F 0)
        (finiteCoherentSpaceProduct n (fun j ↦ F j.succ)))
      (fun j ↦ coherentSpaceTensorProductTotalSnd (F 0)
        (finiteCoherentSpaceProduct n (fun k ↦ F k.succ)) ≫
          finiteCoherentSpaceProductTotalProjection n (fun k ↦ F k.succ) j) i

/-- 各元の全空間射影は同じ元の底射影を厳密に被覆する。 -/
lemma finiteCoherentSpaceProductTotalProjection_base (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
    (i : Fin (n + 1)) : finiteCoherentSpaceProductTotalProjection n F i ≫
      smallLeftUnstraighteningProjection (F i) =
        smallLeftUnstraighteningProjection (finiteCoherentSpaceProduct n F) := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [finiteCoherentSpaceProductTotalProjection, eqToHom_refl,
      Category.id_comp, finiteCoherentSpaceProduct]
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact F2.coherentTransformationTotalMap_projection _ _ _
    · change (_ ≫ _) ≫ _ = _
      rw [Category.assoc, ih]
      exact F2.coherentTransformationTotalMap_projection _ _ _

/-- 元の有限 coherent 積の小さい全空間から、元の有限共通 fiber 積への指定比較。 -/
def finiteCoherentSpaceProductTotalComparison (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})) :
    smallLeftUnstraightening (finiteCoherentSpaceProduct n F) ⟶
      finiteCommonFiberProduct n (fun i ↦ smallLeftUnstraighteningProjection (F i)) :=
  finiteCommonFiberProductLift n (fun i ↦ smallLeftUnstraighteningProjection (F i))
    (finiteCoherentSpaceProductTotalProjection n F)
    (smallLeftUnstraighteningProjection (finiteCoherentSpaceProduct n F))
    (finiteCoherentSpaceProductTotalProjection_base n F)

/-- 元の比較の全成分は、同じ二項射影を反復した元の全空間射影。 -/
lemma finiteCoherentSpaceProductTotalComparison_projection (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
    (i : Fin (n + 1)) : finiteCoherentSpaceProductTotalComparison n F ≫
      finiteCommonFiberProductProjection n
        (fun j ↦ smallLeftUnstraighteningProjection (F j)) i =
          finiteCoherentSpaceProductTotalProjection n F i :=
  finiteCommonFiberProductLift_projection _ _ _ _ _ _

/-- 元の有限比較は元の小さい全空間の底射影を厳密に保持する。 -/
lemma finiteCoherentSpaceProductTotalComparison_base (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})) :
    finiteCoherentSpaceProductTotalComparison n F ≫
      pullback.snd (nonemptyFiniteSSetProductMap n
        (fun i ↦ smallLeftUnstraighteningProjection (F i))) (nonemptyFiniteDiagonal B n) =
          smallLeftUnstraighteningProjection (finiteCoherentSpaceProduct n F) :=
  finiteCommonFiberProductLift_base _ _ _ _ _

end SerrePositivity.InfinityCategories.HomotopyLimits
