module
public import SerrePositivity.KST.SConstruction.SOneObjectClasses
public import SerrePositivity.KST.SConstruction.ZeroRowLoopNaturality

/-! # 元の対象の実際の K 類の自然性
概要：対象の元の K loop 類と BF K 群の加法記法の類は完全関手で像の対象の類へ移る。
方針：S₁ core 比較の π₀ の逆の自然性と、元の loop 射・零次 K 群の表示の自然性を使う。
規約：零対象や S₁ 補完の選択保存は要求しない。使われ方：π₀ K と三角圏 K₀ の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open Spectra
open scoped Simplicial

/-- 元の S₁ core 比較の π₀ の逆は完全関手について自然。 -/
lemma coreSOnePiZeroEquiv_symm_naturality {X Y : StableModel.{u}} (f : X ⟶ Y)
    (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X.carrier : SSet.{u})) :
    SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sPostcompCofiber 1 f.val f.property))
      ((coreSOnePiZeroEquiv X).symm a) =
      (coreSOnePiZeroEquiv Y).symm (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap f.val) a) := by
  apply (coreSOnePiZeroEquiv Y).injective
  change SSet.mapπ₀ (coreSOneComparison Y.carrier)
    (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sPostcompCofiber 1 f.val f.property))
      ((coreSOnePiZeroEquiv X).symm a)) = _
  rw [← SSet.mapπ₀_comp_apply, coreSOneComparison_naturality, SSet.mapπ₀_comp_apply]
  change SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap f.val)
    ((coreSOnePiZeroEquiv X) ((coreSOnePiZeroEquiv X).symm a)) =
      (coreSOnePiZeroEquiv Y) ((coreSOnePiZeroEquiv Y).symm _)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- 元の対象の K loop の成分は完全関手で像の対象の成分へ移る。 -/
lemma objectKPiZeroClass_naturality {X Y : StableModel.{u}} (f : X ⟶ Y) (x : X.carrier _⦋0⦌) :
    SSet.mapπ₀ (boundaryKSpaceFunctor.map f).right (objectKPiZeroClass X x) =
      objectKPiZeroClass Y (f.val.app _ x) := by
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sPostcompCofiber 1 f.val f.property) ≫
      zeroRowLoopComparison 0 Y =
      zeroRowLoopComparison 0 X ≫ (boundaryKSpaceFunctor.map f).right :=
    zeroRowLoopComparison_naturality 0 f
  unfold objectKPiZeroClass
  rw [← SSet.mapπ₀_comp_apply, ← hn, SSet.mapπ₀_comp_apply,
    coreSOnePiZeroEquiv_symm_naturality, SSet.mapπ₀_mk]
  rfl

/-- 零次 K 群の元の π₀ 表示の各同値は完全関手について自然。 -/
lemma kHomotopyZeroPiZeroEquiv_naturality {X Y : StableModel.{u}} (f : X ⟶ Y)
    (a : OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0) :
    kHomotopyZeroPiZeroEquiv Y (kHomotopyMap f 0 a) =
      SSet.mapπ₀ (boundaryKSpaceFunctor.map f).right (kHomotopyZeroPiZeroEquiv X a) := by
  let F := kHomotopyFunctor.{u} 0 ⋙ forget CommGrpCat.{u}
  let G := boundaryKPiZeroFunctor.{u}
  have hn := congrArg (fun g : F.obj X ⟶ G.obj Y => g a)
    (kHomotopyZeroPiZeroIso.{u}.hom.naturality f)
  exact hn

/-- 完全関手の実際の零次 K 群への作用は対象類を像の対象類へ移す。 -/
lemma objectKClass_naturality {X Y : StableModel.{u}} (f : X ⟶ Y) (x : X.carrier _⦋0⦌) :
    Additive.ofMul (kHomotopyMap f 0 (Additive.toMul (objectKClass X x))) =
      objectKClass Y (f.val.app _ x) := by
  apply Additive.toMul.injective
  apply (kHomotopyZeroPiZeroEquiv Y).injective
  change kHomotopyZeroPiZeroEquiv Y
    (kHomotopyMap f 0 (Additive.toMul (objectKClass X x))) = _
  rw [kHomotopyZeroPiZeroEquiv_naturality, objectKClass_piZero, objectKClass_piZero,
    objectKPiZeroClass_naturality]

end SerrePositivity.KST.SConstruction
