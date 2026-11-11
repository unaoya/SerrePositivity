module
public import SerrePositivity.KST.SConstruction.KHomotopyZeroPiZero
public import SerrePositivity.KST.SConstruction.ZeroRowLoopComparison
public import SerrePositivity.KST.SConstruction.SOneComparison
public import SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroLocalization

/-! # 元の S₁ の loop による対象の K 類
概要：S₁ core の比較の π₀ 全単射から、元の K 空間と BF K 群に対象の類を定める。
方針：π₀ 比較の逆と元の零行 loop を合成し、任意の S₁ 補完で同じ類を回収する。
規約：全 gapped S₁ と元の loop 射を保つ。使われ方：π₀ K と三角圏 K₀ の生成元の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open Spectra
open scoped Simplicial

/-- 元の S₁ core の比較は連結成分で全単射。 -/
lemma coreSOneComparison_piZero_bijective (X : StableModel.{u}) :
    Function.Bijective (SSet.mapπ₀ (coreSOneComparison X.carrier)) := by
  have hi := map_isIso_of_trivialKanFibration SSet.π₀Functor
    PiZeroLocalization.inverts_anodyne (coreSOneComparison X.carrier)
  exact (CategoryTheory.isIso_iff_bijective _).mp hi

/-- 元の全 gapped S₁ core の連結成分と元の core の連結成分の同値。 -/
def coreSOnePiZeroEquiv (X : StableModel.{u}) :
    SSet.π₀ (coreSConstruction 1 X.carrier) ≃ SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X.carrier : SSet.{u}) :=
  Equiv.ofBijective _ (coreSOneComparison_piZero_bijective X)

/-- 元の対象を同じ頂点として core に含める。 -/
def objectCoreVertex (X : StableModel.{u}) (x : X.carrier _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X.carrier : SSet.{u}) _⦋0⦌ := ⟨x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex x⟩

/-- 元の対象が定める元の K 空間の loop の連結成分。 -/
def objectKPiZeroClass (X : StableModel.{u}) (x : X.carrier _⦋0⦌) :
    SSet.π₀ (boundaryKSpaceFunctor.obj X).right :=
  SSet.mapπ₀ (zeroRowLoopComparison 0 X)
    ((coreSOnePiZeroEquiv X).symm (SSet.π₀.mk (objectCoreVertex X x)))

/-- 任意の元の S₁ 補完の loop は、その評価対象に定めた類を回収する。 -/
lemma objectKPiZeroClass_sOne (X : StableModel.{u})
    (d : (coreSConstruction 1 X.carrier) _⦋0⦌) :
    objectKPiZeroClass X ((sOneComparison X.carrier).app _ d.val) =
      SSet.π₀.mk ((zeroRowLoopComparison 0 X).app _ d) := by
  have hv : objectCoreVertex X ((sOneComparison X.carrier).app _ d.val) =
      (coreSOneComparison X.carrier).app _ d := Subtype.ext rfl
  unfold objectKPiZeroClass
  rw [hv, ← SSet.mapπ₀_mk]
  change SSet.mapπ₀ (zeroRowLoopComparison 0 X)
    ((coreSOnePiZeroEquiv X).symm ((coreSOnePiZeroEquiv X) (SSet.π₀.mk d))) = _
  rw [Equiv.symm_apply_apply, SSet.mapπ₀_mk]

/-- 同じ対象を評価する二つの元の S₁ 補完は同じ K loop の類を与える。 -/
lemma sOneLoopClass_eq_of_evaluation_eq (X : StableModel.{u})
    (a b : (coreSConstruction 1 X.carrier) _⦋0⦌)
    (h : (sOneComparison X.carrier).app _ a.val = (sOneComparison X.carrier).app _ b.val) :
    SSet.π₀.mk ((zeroRowLoopComparison 0 X).app _ a) =
      SSet.π₀.mk ((zeroRowLoopComparison 0 X).app _ b) := by
  rw [← objectKPiZeroClass_sOne, ← objectKPiZeroClass_sOne, h]

/-- 元の対象が実際の BF K スペクトルの加法記法の零次群に定める類。 -/
def objectKClass (X : StableModel.{u}) (x : X.carrier _⦋0⦌) :
    Additive (OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0) :=
  Additive.ofMul ((kHomotopyZeroPiZeroEquiv X).symm (objectKPiZeroClass X x))

/-- 対象の BF K 類を元の K 空間の π₀ へ戻すと元の loop 類を回収する。 -/
lemma objectKClass_piZero (X : StableModel.{u}) (x : X.carrier _⦋0⦌) :
    (kHomotopyZeroPiZeroEquiv X) (Additive.toMul (objectKClass X x)) =
      objectKPiZeroClass X x :=
  (kHomotopyZeroPiZeroEquiv X).apply_symm_apply _

end SerrePositivity.KST.SConstruction
