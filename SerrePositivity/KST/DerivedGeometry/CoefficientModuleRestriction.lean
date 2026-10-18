module

public import SerrePositivity.KST.DerivedGeometry.CoefficientRestriction
public import SerrePositivity.KST.DerivedGeometry.CoefficientExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-!
概要：実際の係数加群層をスキームの開部分へ制限する。
方針：開集合関手に沿う加群層の pushforward と恒等の係数環層射を使う。
規約：対象の係数環層は既存の restrict そのもの。
使われ方：TT §3・3.19、§8・8.1、Toën §3.2 の T2・T3 の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
variable {X : Scheme.{u}} (B : CoefficientSheaf X) (U : X.Opens)

/-- 概要：開包含の開集合関手は連続。方針：開埋め込みの標準定理を使う。
規約：このファイル内の推論に使う。使われ方：TT 3.19 の開制限。 -/
local instance : U.isOpenEmbedding.functor.IsContinuous
    (Opens.grothendieckTopology U) (Opens.grothendieckTopology X) :=
  U.isOpenEmbedding.functor_isContinuous

/--
概要：係数加群層から開部分の係数加群層への実際の制限関手。
方針：開包含の開集合関手に沿い各切断を制限する。
規約：係数環層の比較射は恒等射。
使われ方：TT 3.19・8.1、Toën §3.2 の局所化と降下。
-/
def openRestriction : B.Modules ⥤ (B.restrict U).Modules :=
  SheafOfModules.pushforward (F := U.isOpenEmbedding.functor) (𝟙 (B.restrict U).ring)

/--
概要：係数加群層の開制限は加法的。
方針：切断上の同じ加法を保持する。
規約：層化で加法を選び直さない。
使われ方：TT 3.19・8.1 の導来制限。
-/
instance openRestriction_additive : (B.openRestriction U).Additive where
  map_add := by intros; rfl

/--
概要：係数加群層の開制限は有限極限を保つ。
方針：加群層の連続関手に沿う pushforward の右随伴性を使う。
規約：係数の平坦性は要求しない。
使われ方：TT 3.19・8.1、Toën §3.2 の導来制限の左完全性。
-/
instance openRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (B.openRestriction U) := by
  dsimp [openRestriction]
  infer_instance

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
