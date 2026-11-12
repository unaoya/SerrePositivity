module

public import SerrePositivity.KST.Spectra.KanSequence
public import SerrePositivity.KST.Spectra.PointedFiber
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
概要：各段が Kan fibration である Kan 列の射の fiber 列。
方針：suspension した fiber 包含と全空間の構造射を合成し、零合成から fiber へ持ち上げる。
規約：ここでは fiber 列の Ω 条件を主張しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。スペクトルの fiber の構成。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.KanSequence

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：suspension は点つき零射を零射へ送る。
方針：円との smash が左随伴であることによる零射保存を使う。
規約：通常の点つき圏の等式。
使われ方：BF 1978 §2、HA §1.4.2。fiber への構造射の零合成。 -/
theorem suspension_zero (A B : PointedSimplicialSet.{u}) :
    PointedSimplicialSet.circle.{u} ◁ (0 : A ⟶ B) = 0 :=
  (tensorLeft PointedSimplicialSet.circle.{u}).map_zero _ _

/-- 概要：fiber の suspension から次段の全空間への構造射は底への合成が零。
方針：列の可換性と fiber 包含の零合成、suspension の零射保存を使う。
規約：fiber の構造射の定義に用いる厳密な等式。
使われ方：Goerss–Jardine I §7、BF 1978 §2。段の fiber の貼り合わせ。 -/
theorem Hom.fiber_sigma_zero {X Y : KanSequence.{u}} (p : Hom X Y) (n : ℕ) :
    (PointedSimplicialSet.circle.{u} ◁ pointedFiberι (p.app n) ≫ X.sigma n) ≫ p.app (n + 1) =
      0 := by
  rw [Category.assoc, ← p.comm n, ← Category.assoc, ← whiskerLeft_comp,
    pointedFiberι_comp, suspension_zero, zero_comp]

/-- 概要：各段の fiber の suspension 構造射。
方針：suspension した包含と元の構造射の合成を fiber へ持ち上げる。
規約：この射の単射性は要求しない。
使われ方：BF 1978 §2、HA §1.4.2。置換前の fiber 列。 -/
def Hom.fiberSigma {X Y : KanSequence.{u}} (p : Hom X Y) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (pointedFiber (p.app n)) ⟶ pointedFiber (p.app (n + 1)) :=
  pointedFiberLiftOfZero (p.app (n + 1))
    (PointedSimplicialSet.circle.{u} ◁ pointedFiberι (p.app n) ≫ X.sigma n) (p.fiber_sigma_zero n)

/-- 概要：各段が Kan fibration である射の点つき fiber の Kan 列。
方針：各 fiber の Kan 性と構成済みの構造射を束ねる。
規約：Ω 条件と cofibrant 条件はこの定義ではまだ主張しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。スペクトルの fiber の前段階。 -/
def Hom.fiber {X Y : KanSequence.{u}} (p : Hom X Y) (hp : ∀ n, Fibration (p.app n).right) :
    KanSequence.{u} where
  level n := {
    space := pointedFiber (p.app n)
    kan := @pointedFiber_kanComplex (X.level n).space (Y.level n).space (p.app n) (hp n) }
  sigma := p.fiberSigma

/-- 概要：fiber の Kan 列から全空間の列への厳密な包含射。
方針：各段の fiber 包含と持ち上げの計算式を使う。
規約：構造射と厳密可換。
使われ方：Goerss–Jardine I §7、BF 1978 §2。fiber 列の最初の射。 -/
def Hom.fiberInclusion {X Y : KanSequence.{u}} (p : Hom X Y)
    (hp : ∀ n, Fibration (p.app n).right) : Hom (p.fiber hp) X where
  app n := pointedFiberι (p.app n)
  comm n := (pointedFiberLiftOfZero_ι (p.app (n + 1))
    (PointedSimplicialSet.circle.{u} ◁ pointedFiberι (p.app n) ≫ X.sigma n)
      (p.fiber_sigma_zero n)).symm

end

end SerrePositivity.KST.Spectra.KanSequence
