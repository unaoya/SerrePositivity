module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleAugmentedPullback
public import SerrePositivity.HomologicalAlgebra.Cech.Basic

/-!
概要：同じ実際の増大係数図式を、B1 の既存の複体関手へ渡す。
方針：増大 cochain 関手の代入と、元の複体の射の可換性を使う。
規約：同じ基底項・タプル係数・引き戻しの全ての写像を保つ。
使われ方：B1 の可換な微分の二重複体への実際の入力。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped Simplicial
universe u
variable {R : Type u} [CommRing R] {Y : Scheme.{u}}
variable (g : Y ⟶ Spec (CommRingCat.of R)) {ι : Type} [Fintype ι] [DecidableEq ι]
variable (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

/-- 同じ増大項とタプル係数の図式を、B1 の既存の増大 cochain 関手で写した値。 -/
def schemePerfectCechTupleDouble :
    CochainComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ) ℕ :=
  SerrePositivity.Cech.augmentedCochain.obj (schemePerfectCechTupleAugmented g U p hp hR)

/-- 水平方向の零次項は、同じ基底の Frobenius 順極限の single。 -/
theorem schemePerfectCechTupleDouble_zero :
    (schemePerfectCechTupleDouble g U p hp hR).X 0 =
      (HomologicalComplex.single (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) 0).obj
        (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR)) := rfl

/-- 水平方向の後続項は、同じ nerve のタプル係数複体。 -/
theorem schemePerfectCechTupleDouble_succ (n : ℕ) :
    (schemePerfectCechTupleDouble g U p hp hR).X (n + 1) =
      schemePerfectCechTupleComplex g U p hp
        (schemeCechNervePresheaf_primeCast g p hR) ⦋n⦌ := rfl

/-- 水平微分は、同じ既存の増大射と交代余面微分。 -/
theorem schemePerfectCechTupleDouble_horizontal (n : ℕ) :
    (schemePerfectCechTupleDouble g U p hp hR).d n (n + 1) =
      SerrePositivity.Cech.differential (schemePerfectCechTupleAugmented g U p hp hR) n :=
  SerrePositivity.Cech.augmentedCochain_d _ n

/-- 二方向の微分の可換性は、同じ係数複体の射の可換性そのもの。 -/
theorem schemePerfectCechTupleDouble_comm (n j k : ℕ) :
    ((schemePerfectCechTupleDouble g U p hp hR).X n).d j k ≫
        ((schemePerfectCechTupleDouble g U p hp hR).d n (n + 1)).f k =
      ((schemePerfectCechTupleDouble g U p hp hR).d n (n + 1)).f j ≫
        ((schemePerfectCechTupleDouble g U p hp hR).X (n + 1)).d j k :=
  (((schemePerfectCechTupleDouble g U p hp hR).d n (n + 1)).comm j k).symm

variable {S : Type u} [CommRing S] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (F : Arrow.mk f ⟶ Arrow.mk g)
variable (q : R →+* S) (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable (hS : (p : S) = 0)

/-- 同じ増大係数図式の実際の引き戻しを、既存の複体関手で写した射。 -/
def schemePerfectCechTupleDoublePullback :
    schemePerfectCechTupleDouble g U p hp hR ⟶
      schemePerfectCechTupleDouble f (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS :=
  SerrePositivity.Cech.augmentedCochain.map
    (schemePerfectCechTupleAugmentedPullback f g F q hq U p hp hR hS)

/-- 水平零次の射は、同じ基底環の実際の Frobenius 係数写像の single。 -/
theorem schemePerfectCechTupleDoublePullback_zero :
    (schemePerfectCechTupleDoublePullback g U p hp hR f F q hq hS).f 0 =
      (HomologicalComplex.single (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) 0).map
        (ModuleCat.ofHom (frobeniusDirectLimitMap p hp hR hS q).toAddMonoidHom.toIntLinearMap) :=
  rfl

/-- 水平後続次数の射は、同じタプル被覆の実際の引き戻し。 -/
theorem schemePerfectCechTupleDoublePullback_succ (n : ℕ) :
    (schemePerfectCechTupleDoublePullback g U p hp hR f F q hq hS).f (n + 1) =
      schemePerfectCechTuplePullbackMap F U p hp
        (schemeCechNervePresheaf_primeCast f p hS)
        (schemeCechNervePresheaf_primeCast g p hR) ⦋n⦌ := rfl

end SerrePositivity.AlgebraicGeometry
