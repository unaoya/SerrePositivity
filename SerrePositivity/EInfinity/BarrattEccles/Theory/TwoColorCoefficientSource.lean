module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.ArityProjectiveResolution
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorPermutation
public import Mathlib.RepresentationTheory.Coinduced

/-!
# 二色の係数解像度の始域

## 概要
HA 3.2.4.7 の二色比較のため、実際の arity の解像度を二色の置換部分群へ制限する。

## 方針
単射なブロック置換の像を部分群として使い、制限の射影性とホモロジーの保存を適用する。

## 規約
部分群と Σ_m × Σ_n の同型を指定し、両色への射影はその逆から作る。

## 使われ方
二色の係数複体の共通の表現の圏と、指定比較射の始域の射影解像度。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory

/-- 二色のブロック置換がなす実際の部分群。 -/
abbrev TwoColorGroup (m n : ℕ) := (twoColorPermutationHom.{u} m n).range

/-- 二色の置換群の直積と、そのブロック置換部分群の指定同型。 -/
def twoColorGroupEquiv (m n : ℕ) :
    ULift.{u} (Equiv.Perm (Fin m) × Equiv.Perm (Fin n)) ≃* TwoColorGroup.{u} m n :=
  MonoidHom.ofInjective (twoColorPermutationHom_injective.{u} m n)

/-- 二色部分群から第一の色の置換群への射影。 -/
def twoColorLeftProjection (m n : ℕ) : TwoColorGroup.{u} m n →* ULift.{u} (Equiv.Perm (Fin m)) where
  toFun g := ULift.up ((twoColorGroupEquiv m n).symm g).down.1
  map_one' := by rw [map_one]; rfl
  map_mul' g h := by rw [map_mul]; rfl

/-- 二色部分群から第二の色の置換群への射影。 -/
def twoColorRightProjection (m n : ℕ) :
    TwoColorGroup.{u} m n →* ULift.{u} (Equiv.Perm (Fin n)) where
  toFun g := ULift.up ((twoColorGroupEquiv m n).symm g).down.2
  map_one' := by rw [map_one]; rfl
  map_mul' g h := by rw [map_mul]; rfl

/-- 指定されたブロック同型と第一の射影の照合。 -/
lemma twoColorLeftProjection_block (m n : ℕ)
    (g : ULift.{u} (Equiv.Perm (Fin m) × Equiv.Perm (Fin n))) :
    twoColorLeftProjection m n (twoColorGroupEquiv m n g) = ULift.up g.down.1 := by
  change ULift.up ((twoColorGroupEquiv m n).symm (twoColorGroupEquiv m n g)).down.1 = _
  rw [MulEquiv.symm_apply_apply]

/-- 指定されたブロック同型と第二の射影の照合。 -/
lemma twoColorRightProjection_block (m n : ℕ)
    (g : ULift.{u} (Equiv.Perm (Fin m) × Equiv.Perm (Fin n))) :
    twoColorRightProjection m n (twoColorGroupEquiv m n g) = ULift.up g.down.2 := by
  change ULift.up ((twoColorGroupEquiv m n).symm (twoColorGroupEquiv m n g)).down.2 = _
  rw [MulEquiv.symm_apply_apply]

variable (A : Type u) [CommRing A]

/-- 二色比較の共通の増大の値となる、自明表現の制限。 -/
def twoColorTrivialRepresentation (m n : ℕ) : Rep.{u} A (TwoColorGroup.{u} m n) :=
  (Rep.resFunctor.{u} (k := A) (twoColorPermutationHom.{u} m n).range.subtype).obj
    (Rep.trivial A (ULift.{u} (Equiv.Perm (Fin (m + n)))) (𝟙_ (ModuleCat A)))

/-- 二色の係数比較の始域は、指定増大を持つ射影解像度である。 -/
def twoColorSourceResolution (m n : ℕ) :
    ProjectiveResolution (twoColorTrivialRepresentation A m n) :=
  (Rep.resFunctor.{u} (k := A)
    (twoColorPermutationHom.{u} m n).range.subtype).mapProjectiveResolution
    (arityProjectiveResolution A (m + n))

end SerrePositivity.EInfinity.BarrattEccles
