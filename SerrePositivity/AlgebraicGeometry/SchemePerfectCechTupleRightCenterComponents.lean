module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleLeftTotalComponents
public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareRightComponents

/-!
概要：元のF8の中心側と、中心自身の恒等矢印の左側との次数ごとの比較。
方針：元の中心の座標には負、Eの縦b次には(-1)^bを掛ける。
規約：同じ逆像被覆を用い、ここでは鎖写像性をまだ主張しない。
使われ方：中心側の元の核の完全性をNoether帰納へ接続する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
local notation "up" => ComplexShape.up ℕ
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

/-- 中心の恒等Arrowに用いる、同じ環の恒等射のSpecとの照合。 -/
theorem schemePerfectCechTupleCenterIdentity_right :
    Arrow.Hom.right (𝟙 (Arrow.mk f)) = Spec.map (CommRingCat.ofHom (RingHom.id S)) := by
  simp

/-- 中心の同じ逆像被覆と恒等Arrowから得る、既存のY側の二重複体。 -/
abbrev schemePerfectCechTupleCenterLeftDouble : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up :=
  schemePerfectCechTupleSquareLeftPositiveDouble f f (𝟙 _) (RingHom.id S)
    (schemePerfectCechTupleCenterIdentity_right f) (fun i ↦ (F.left ⁻¹ᵁ U i)) p hp hS hS

/-- 元のF8の中心側の同じ二重複体。 -/
abbrev schemePerfectCechTupleRightPositiveDouble : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up :=
  (AlgebraicTopology.alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ)).obj
    (schemePerfectCechTupleSquareRightFunctor f g F q hq U p hp hR hS)

set_option backward.isDefEq.respectTransparency false in
/-- 元の各頂点で、中心に負、Eの縦b次に(-1)^bを掛ける同じ射。 -/
def schemePerfectCechTupleRightCenterForwardVertex (a b : ℕ) :
    ((schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS).X a).X b ⟶
      ((schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS).X a).X (b + 1) := by
  let s := schemePerfectCechTupleSquare f g F q hq U p hp hR hS ⦋a⦌
  let t := schemePerfectCechTupleSquare f f (𝟙 _) (RingHom.id S)
    (schemePerfectCechTupleCenterIdentity_right f) (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS hS ⦋a⦌
  cases b with
  | zero => exact -s.rightCenterι
  | succ b => exact ((-1 : ℤ) ^ b) • (t.leftCπ b ≫ s.rightEι b)

set_option backward.isDefEq.respectTransparency false in
/-- 元の各頂点の同じ符号つきの逆向きの射。 -/
def schemePerfectCechTupleRightCenterBackwardVertex (a b : ℕ) :
    ((schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS).X a).X (b + 1) ⟶
      ((schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS).X a).X b := by
  let s := schemePerfectCechTupleSquare f g F q hq U p hp hR hS ⦋a⦌
  let t := schemePerfectCechTupleSquare f f (𝟙 _) (RingHom.id S)
    (schemePerfectCechTupleCenterIdentity_right f) (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS hS ⦋a⦌
  cases b with
  | zero => exact -s.rightCenterπ
  | succ b => exact ((-1 : ℤ) ^ b) • (s.rightEπ b ≫ t.leftCι b)

set_option backward.isDefEq.respectTransparency false in
/-- 中心の左側の各脚を、一つ先の元の右側の全次数へ送る符号つきの射。 -/
def schemePerfectCechTupleRightCenterForwardSummand (a b n : ℕ)
    (h : ComplexShape.π up up up (a, b) = n) :
    ((schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS).X a).X b ⟶
      ((schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS).total up).X (n + 1) :=
  schemePerfectCechTupleRightCenterForwardVertex f g F q hq U p hp hR hS a b ≫
    (schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS).ιTotal up a (b + 1) (n + 1)
      (by change a + b = n at h; change a + (b + 1) = n + 1; omega)

/-- 同じtotalDescで各脚をまとめた、次数を一つ上げる比較射。 -/
def schemePerfectCechTupleRightCenterForwardComponent (n : ℕ) :
    ((schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS).total up).X n ⟶
      ((schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS).total up).X (n + 1) :=
  (schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS).totalDesc
    (fun a b h ↦ schemePerfectCechTupleRightCenterForwardSummand f g F q hq U p hp hR hS a b n h)

/-- 同じ全次数の各直和入射に沿った前向き比較射の式。 -/
theorem ι_schemePerfectCechTupleRightCenterForwardComponent (a b n : ℕ)
    (h : ComplexShape.π up up up (a, b) = n) :
    (schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS).ιTotal up a b n h ≫
      schemePerfectCechTupleRightCenterForwardComponent f g F q hq U p hp hR hS n =
        schemePerfectCechTupleRightCenterForwardSummand f g F q hq U p hp hR hS a b n h :=
  HomologicalComplex₂.ι_totalDesc _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- 元の右側の各脚を、同じ中心の左側の一つ前の全次数へ戻す射。 -/
def schemePerfectCechTupleRightCenterBackwardSummand (a b n : ℕ)
    (h : ComplexShape.π up up up (a, b) = n + 1) :
    ((schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS).X a).X b ⟶
      ((schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS).total up).X n := by
  cases b with
  | zero => exact 0
  | succ b =>
    exact schemePerfectCechTupleRightCenterBackwardVertex f g F q hq U p hp hR hS a b ≫
      (schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS).ιTotal up a b n
        (by change a + (b + 1) = n + 1 at h; change a + b = n; omega)

/-- 元の右側の同じtotalDescでまとめた逆向きの次数ごとの射。 -/
def schemePerfectCechTupleRightCenterBackwardComponent (n : ℕ) :
    ((schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS).total up).X (n + 1) ⟶
      ((schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS).total up).X n :=
  (schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS).totalDesc
    (fun a b h ↦ schemePerfectCechTupleRightCenterBackwardSummand f g F q hq U p hp hR hS a b n h)

/-- 同じ各直和入射に沿った逆向き比較射の式。 -/
theorem ι_schemePerfectCechTupleRightCenterBackwardComponent (a b n : ℕ)
    (h : ComplexShape.π up up up (a, b) = n + 1) :
    (schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS).ιTotal up a b (n + 1) h ≫
      schemePerfectCechTupleRightCenterBackwardComponent f g F q hq U p hp hR hS n =
        schemePerfectCechTupleRightCenterBackwardSummand f g F q hq U p hp hR hS a b n h :=
  HomologicalComplex₂.ι_totalDesc _ _ _ _ _

end SerrePositivity.AlgebraicGeometry
