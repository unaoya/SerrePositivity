module

public import SerrePositivity.KST.Spectra.TotalizationFunctor

/-!
概要：通常の Tot による Reedy horn RLP の Kan fibration への移送。
方針：Tot の持ち上げ問題をパラメーター付き余単体射へ戻し、Reedy 次数帰納で解く。
規約：係数の各値の Kan 性を別に仮定せず、相対 matching 条件を使う。
使われ方：Goerss–Jardine VII §4、VIII §1。Tot の塔とホモトピー比較の充填。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open HomotopicalAlgebra SSet SSet.modelCategoryQuillen
open SerrePositivity.Reedy
open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra.CosimplicialTotalization

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance totalizationFibrationSelfEnrichment : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
  enrichedOrdinaryCategorySelf SSet.{u}

lemma uncurry_pre {X : CosimplicialObject SSet.{u}} {A B : SSet.{u}}
    (i : A ⟶ B) (a : B ⟶ obj X) :
    uncurry (i ≫ a) = SimplexTensorBoundary.map i ≫ uncurry a := by
  apply NatTrans.ext
  funext j
  change MonoidalClosed.uncurry ((i ≫ a) ≫ π X j) =
    (SSet.stdSimplex.obj j ◁ i) ≫ MonoidalClosed.uncurry (a ≫ π X j)
  rw [Category.assoc, uncurry_natural_left]

lemma uncurry_map {X Y : CosimplicialObject SSet.{u}} {A : SSet.{u}}
    (a : A ⟶ obj X) (f : X ⟶ Y) : uncurry (a ≫ map f) = uncurry a ≫ f := by
  apply NatTrans.ext
  funext j
  change MonoidalClosed.uncurry ((a ≫ map f) ≫ π Y j) =
    MonoidalClosed.uncurry (a ≫ π X j) ≫ f.app j
  rw [Category.assoc, map_π, ← Category.assoc, uncurry_natural_right]

lemma lift_post {X Y : CosimplicialObject SSet.{u}} {A : SSet.{u}}
    (s : SimplexTensorBoundary.diagram A ⟶ X) (f : X ⟶ Y) :
    lift s ≫ map f = lift (s ≫ f) := by
  apply end_.hom_ext
  intro j
  change (lift s ≫ map f) ≫ π Y j = lift (s ≫ f) ≫ π Y j
  rw [Category.assoc, map_π, ← Category.assoc, lift_π, lift_π]
  exact (curry_natural_right (s.app j) (f.app j)).symm

/-- 概要：Reedy horn RLP な係数の射は Tot 上の Kan fibration を誘導する。
方針：horn を tensor した標準単体の相対 latching が anodyne なことを使う。
規約：右類は実際の horn の右持ち上げ性。
使われ方：Goerss–Jardine VII §4、VIII §1。Tot の相対充填。 -/
lemma map_fibration {X Y : CosimplicialObject SSet.{u}} (f : X ⟶ Y)
    (hf : reedyRight simplex J.rlp f) : Fibration (map f) := by
  let := CosimplicialHornFactorization.hornWeakFactorization.{u}
  apply (fibration_iff _).mpr
  intro A B i hi
  have hai : anodyneExtensions i := by
    rw [anodyneExtensions_eq_llp_rlp]
    exact MorphismProperty.le_llp_rlp J i hi
  have hir := SimplexTensorBoundary.map_reedy_anodyne i hai
  let : ∀ j, HasLiftingProperty
      (relativeLatchingMap simplex j (SimplexTensorBoundary.map i))
      (relativeMatchingMap simplex j f) :=
    fun j ↦ MorphismProperty.hasLiftingProperty_of_wfs _ _ (hir j) (hf j)
  let : HasLiftingProperty (SimplexTensorBoundary.map i) f := Lifting.hasLiftingProperty simplex
  refine ⟨fun {a b} sq ↦ ?_⟩
  let q : CommSq (uncurry a) (SimplexTensorBoundary.map i) f (uncurry b) :=
    ⟨by
      rw [← uncurry_map, ← uncurry_pre]
      exact congrArg uncurry sq.w⟩
  refine ⟨⟨{ l := lift q.lift, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [lift_pre, q.fac_left, lift_uncurry]
  · rw [lift_post, q.fac_right, lift_uncurry]

end

end SerrePositivity.KST.Spectra.CosimplicialTotalization
