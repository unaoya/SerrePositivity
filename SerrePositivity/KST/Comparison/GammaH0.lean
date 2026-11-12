module

public import SerrePositivity.KST.Comparison.GammaRing
public import SerrePositivity.KST.Comparison.PiZeroRing
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedPiZero
public import SerrePositivity.DifferentialGraded.Category.Basic

/-!
# Γ の連結成分と H⁰

概要：Γ の連結成分を dg 圏の H⁰ の射および実際の次数零ホモロジーに同定する。
方針：標準 DK 模型から既存の dg nerve の写像空間への同型と π₀ の比較を合成する。
規約：係数と対象を同じ宇宙に置く。dg 代数の一対象模型はこの条件を満たす。
使われ方：SS03 Proposition 2.13、KST §2.2 の π₀A と H⁰(A) の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.Comparison

open CategoryTheory DifferentialGraded SSet


/--
概要：同一宇宙内の ULift は元の単体集合と同型である。
方針：各次数で up と down を使う。
規約：SSet.uliftFunctor の実際の面・退化の定義と可換。
使われ方：SS03 (2.9) の小さい標準模型と dg nerve の比較の宇宙調整。
-/
def sameUniverseLiftIso (X : SSet.{u}) : SSet.uliftFunctor.{u, u}.obj X ≅ X where
  hom := { app := fun _ => TypeCat.ofHom ULift.down, naturality := fun _ _ _ => rfl }
  inv := { app := fun _ => TypeCat.ofHom ULift.up, naturality := fun _ _ _ => rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

variable {R : Type u} [CommRing R] {D : Type u} [DGCategory R D]

/--
概要：AW 自己 Hom 環の台は dg nerve の右 pinched 自己 Hom と同型である。
方針：標準座標の同型、宇宙の同型、既存の線形 Hom の比較を合成する。
規約：この同型は単体集合の同型。SS03 (2.9) の Γ と H⁰ の接続用。
使われ方：連結成分の比較同値。
-/
def gammaEndPinchedIso (x : D) : ringSpace (gammaEndRingObject (R := R) x) ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x x :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpaceStandardIso (R := R) x x).symm ≪≫
    (sameUniverseLiftIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpace (R := R) x x)).symm ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpaceLiftIso (R := R) x x

/--
概要：Γ の連結成分を dg 圏の H⁰ の自己射に同定する。
方針：単体集合の同型を π₀ に送り、既存の H⁰ 比較と合成する。
規約：KST §2.2 の成分環の台の同定。乗法の保存は別途証明する。
使われ方：dg 代数の π₀ の H⁰ による表示。
-/
def gammaEndPiZeroH0Equiv (x : D) : π₀ (ringSpace (gammaEndRingObject (R := R) x)) ≃
    ((toHomotopy R D).obj (ForgetEnrichment.of (Complex R) x) ⟶
      (toHomotopy R D).obj (ForgetEnrichment.of (Complex R) x)) :=
  (π₀Functor.mapIso (gammaEndPinchedIso (R := R) x)).toEquiv.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.piZeroEquiv x x)

/--
概要：Γ の連結成分を実際の Mathlib の H⁰ の台に同定する。
方針：H⁰ の射の同定と既存の cycles/boundaries 商から homology への同定を合成する。
規約：SS03 Proposition 2.13 の NΓ と切断複体の同一視と整合させる入口。
使われ方：connective dg 代数の成分環のホモロジー表示。
-/
def gammaEndPiZeroHomologyEquiv (x : D) : π₀ (ringSpace (gammaEndRingObject (R := R) x)) ≃
    (homObject R D x x).homology 0 :=
  (gammaEndPiZeroH0Equiv (R := R) x).trans
    (homotopyHomologyEquiv R D (ForgetEnrichment.of (Complex R) x)
      (ForgetEnrichment.of (Complex R) x))

end SerrePositivity.KST.Comparison
