module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleRightCenterHorizontal
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleRightCenterRetraction
public import SerrePositivity.AlgebraicGeometry.CechIntegerTotalVerticalSucc
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
概要：元の中心側のwhole totalは、中心の左側のwhole totalのunsigned successorと同型。
方針：同じ各次数の正逆と二方向の微分の式をisoOfComponentsへ代入する。
規約：元の右側の零次の零性を使い、整数添字のsigned shiftは用いない。
使われ方：中心の帰納仮定を元のF8の右側の核の完全性へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ZeroObject Simplicial
universe u
local notation "up" => ComplexShape.up ℕ
local notation "ee" => ComplexShape.embeddingUp'Add (1 : ℕ) 1
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 元の中心側の次数を一つ上げる比較は、元のwhole totalの微分と可換。 -/
theorem schemePerfectCechTupleRightCenterForwardComponent_d (n : ℕ) :
    schemePerfectCechTupleRightCenterForwardComponent f g F q hq U p hp hR hS n ≫
      ((schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS).total up).d (n + 1) (n + 2) =
    ((schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS).total up).d n (n + 1) ≫
      schemePerfectCechTupleRightCenterForwardComponent f g F q hq U p hp hR hS (n + 1) :=
  cechIntegerTotalVerticalSuccComponent_d _ _
    (schemePerfectCechTupleRightCenterForwardVertex f g F q hq U p hp hR hS)
    (schemePerfectCechTupleRightCenterForwardVertex_horizontal f g F q hq U p hp hR hS)
    (schemePerfectCechTupleRightCenterForwardVertex_vertical f g F q hq U p hp hR hS) n

set_option backward.isDefEq.respectTransparency false in
/-- 元の中心側のwhole totalの零次は、同じ各脚が零なので零対象。 -/
theorem schemePerfectCechTupleRightTotal_isZero_zero :
    IsZero (((schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS).total up).X 0) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  have ha : a = 0 := by change a + b = 0 at h; omega
  have hb : b = 0 := by change a + b = 0 at h; omega
  subst a
  subst b
  have hz : IsZero (((schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS).X 0).X 0) := by
    change IsZero (0 : ModuleCat.{u} ℤ)
    exact isZero_zero _
  exact hz.eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
/-- 元の右側のwhole totalと中心の左側のunsigned successorとの、同じ座標の複体の同型。 -/
def schemePerfectCechTupleRightCenterTotalIso :
    ((schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS).total up).extend ee ≅
      (schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS).total up := by
  let K : CochainComplex (ModuleCat.{u} ℤ) ℕ :=
    (schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS).total up
  let L : CochainComplex (ModuleCat.{u} ℤ) ℕ :=
    (schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS).total up
  have hz : IsZero ((K.extend ee).X 0) := K.isZero_extend_X ee 0 (by intro i; change i + 1 ≠ 0; omega)
  let eS (n : ℕ) : K.X n ≅ L.X (n + 1) :=
    { hom := schemePerfectCechTupleRightCenterForwardComponent f g F q hq U p hp hR hS n
      inv := schemePerfectCechTupleRightCenterBackwardComponent f g F q hq U p hp hR hS n
      hom_inv_id := schemePerfectCechTupleRightCenterForward_backward f g F q hq U p hp hR hS n
      inv_hom_id := schemePerfectCechTupleRightCenterBackward_forward f g F q hq U p hp hR hS n }
  refine HomologicalComplex.Hom.isoOfComponents (fun n ↦ match n with
    | 0 => hz.iso (schemePerfectCechTupleRightTotal_isZero_zero f g F q hq U p hp hR hS)
    | n + 1 => K.extendXIso ee (i := n) rfl ≪≫ eS n) ?_
  intro n m hnm
  have hm : n + 1 = m := hnm
  subst m
  cases n with
  | zero => exact hz.eq_of_src _ _
  | succ n =>
    let e : ComplexShape.Embedding up up := ee
    let t₀ : (K.extend e).X (n + 1) ≅ K.X n :=
      K.extendXIso e (i := n) (i' := n + 1) rfl
    let t₁ : (K.extend e).X (n + 2) ≅ K.X (n + 1) :=
      K.extendXIso e (i := n + 1) (i' := n + 2) rfl
    let δ : K.X n ⟶ L.X (n + 1) :=
      schemePerfectCechTupleRightCenterForwardComponent f g F q hq U p hp hR hS n
    let δ' : K.X (n + 1) ⟶ L.X (n + 2) :=
      schemePerfectCechTupleRightCenterForwardComponent f g F q hq U p hp hR hS (n + 1)
    have hd : (K.extend e).d (n + 1) (n + 2) = t₀.hom ≫ K.d n (n + 1) ≫ t₁.inv :=
      K.extend_d_eq e (i := n) (j := n + 1) (i' := n + 1) (j' := n + 2) rfl rfl
    have hh : δ ≫ L.d (n + 1) (n + 2) = K.d n (n + 1) ≫ δ' :=
      schemePerfectCechTupleRightCenterForwardComponent_d f g F q hq U p hp hR hS n
    change (t₀.hom ≫ δ) ≫ L.d (n + 1) (n + 2) = (K.extend e).d (n + 1) (n + 2) ≫ (t₁.hom ≫ δ')
    calc
      _ = t₀.hom ≫ (δ ≫ L.d (n + 1) (n + 2)) := Category.assoc _ _ _
      _ = t₀.hom ≫ (K.d n (n + 1) ≫ δ') :=
        congrArg (fun z : K.X n ⟶ L.X (n + 2) ↦ t₀.hom ≫ z) hh
      _ = (t₀.hom ≫ K.d n (n + 1) ≫ t₁.inv) ≫ (t₁.hom ≫ δ') := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = (K.extend e).d (n + 1) (n + 2) ≫ (t₁.hom ≫ δ') :=
        congrArg (fun z : (K.extend e).X (n + 1) ⟶ (K.extend e).X (n + 2) ↦ z ≫ (t₁.hom ≫ δ')) hd.symm

end SerrePositivity.AlgebraicGeometry
