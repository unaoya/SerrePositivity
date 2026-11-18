module

public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareLeftComponents
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleSquareLeftRight
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleDouble
public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotal

/-!
概要：元の増大二重Čechから同じF8のY側への、全次数を保つ直和の射。
方針：元の各ιTotalと同じCの座標の包含で各項を再索引する。
規約：ここでは次数ごとの射だけを作り、複体の同型とはまだ主張しない。
使われ方：元の核のtotalへ持ち上げる比較の微分・逆射の照合。
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

/-- 同じF8のY側の図式の交代余面複体。 -/
abbrev schemePerfectCechTupleSquareLeftPositiveDouble :
    HomologicalComplex₂ (ModuleCat.{u} ℤ) up up :=
  (alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ)).obj
    (schemePerfectCechTupleSquareLeftFunctor f g F q hq U p hp hR hS)

set_option backward.isDefEq.respectTransparency false in
/-- 元の各項を同じ全次数のY側の項へ入れる、直和の各脚。 -/
def schemePerfectCechTupleLeftTotalSummand (a b n : ℕ)
    (h : ComplexShape.π up up up (a, b) = n) :
    ((schemePerfectCechTupleDouble g U p hp hR).X a).X b ⟶
      ((schemePerfectCechTupleSquareLeftPositiveDouble f g F q hq U p hp hR hS).total up).X n := by
  let L := schemePerfectCechTupleSquareLeftPositiveDouble f g F q hq U p hp hR hS
  cases a with
  | zero =>
    cases b with
    | zero =>
      have hn : n = 0 := by change 0 + 0 = n at h; omega
      subst n
      exact (HomologicalComplex.singleObjXSelf up 0
        (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))).hom ≫
        L.ιTotal up 0 0 0 (by rfl)
    | succ b => exact 0
  | succ a =>
    exact (schemePerfectCechTupleSquare f g F q hq U p hp hR hS ⦋a⦌).leftCι b ≫
      L.ιTotal up a (b + 1) n (by change a + 1 + b = n at h; change a + (b + 1) = n; omega)

/-- 同じ元のtotalDescに各脚を入れた、各全次数の射。 -/
def schemePerfectCechTupleLeftTotalComponent (n : ℕ) :
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (schemePerfectCechTupleDouble g U p hp hR) up).X n ⟶
      ((schemePerfectCechTupleSquareLeftPositiveDouble f g F q hq U p hp hR hS).total up).X n :=
  HomologicalComplex₂.totalDesc (c₁₂ := up) (schemePerfectCechTupleDouble g U p hp hR)
    (fun a b h ↦ schemePerfectCechTupleLeftTotalSummand f g F q hq U p hp hR hS a b n h)

/-- 各元の直和入射で比較すると、指定した同じ再索引の脚になる。 -/
theorem ι_schemePerfectCechTupleLeftTotalComponent (a b n : ℕ)
    (h : ComplexShape.π up up up (a, b) = n) :
    HomologicalComplex₂.ιTotal (schemePerfectCechTupleDouble g U p hp hR) up a b n h ≫
        schemePerfectCechTupleLeftTotalComponent f g F q hq U p hp hR hS n =
      schemePerfectCechTupleLeftTotalSummand f g F q hq U p hp hR hS a b n h :=
  HomologicalComplex₂.ι_totalDesc _ _ _ _ _


private theorem cechLeftComponent_sum_f
    {A B : CochainComplex (ModuleCat.{u} ℤ) ℕ} {α : Type} [Fintype α]
    (v : α → (A ⟶ B)) (b : ℕ) : (∑ i, v i).f b = ∑ i, (v i).f b :=
  map_sum (HomologicalComplex.Hom.fAddMonoidHom b) v Finset.univ

set_option backward.isDefEq.respectTransparency false in
/-- 元のCの座標の包含は、同じ余面の交代和からなる水平微分と可換。 -/
theorem schemePerfectCechTupleLeftCι_horizontal (a b : ℕ) :
    (schemePerfectCechTupleSquare f g F q hq U p hp hR hS ⦋a⦌).leftCι b ≫
        ((schemePerfectCechTupleSquareLeftPositiveDouble f g F q hq U p hp hR hS).d a (a + 1)).f
          (b + 1) =
      ((schemePerfectCechTupleDouble g U p hp hR).d (a + 1) (a + 2)).f b ≫
        (schemePerfectCechTupleSquare f g F q hq U p hp hR hS ⦋a + 1⦌).leftCι b := by
  have hL : (schemePerfectCechTupleSquareLeftPositiveDouble f g F q hq U p hp hR hS).d a (a + 1) =
      AlternatingCofaceMapComplex.objD
        (schemePerfectCechTupleSquareLeftFunctor f g F q hq U p hp hR hS) a :=
    CochainComplex.of_d
      (fun n ↦ (schemePerfectCechTupleSquareLeftFunctor f g F q hq U p hp hR hS).obj ⦋n⦌)
      (AlternatingCofaceMapComplex.objD
        (schemePerfectCechTupleSquareLeftFunctor f g F q hq U p hp hR hS)) a
  rw [hL, schemePerfectCechTupleDouble_horizontal g U p hp hR (a + 1)]
  change _ ≫ (∑ i : Fin (a + 2), (-1 : ℤ) ^ (i : ℕ) •
      (schemePerfectCechTupleSquareLeftFunctor f g F q hq U p hp hR hS).map (SimplexCategory.δ i)).f (b + 1) =
    (∑ i : Fin (a + 2), (-1 : ℤ) ^ (i : ℕ) •
      (schemePerfectCechTupleFunctor g U p hp (schemeCechNervePresheaf_primeCast g p hR)).map (SimplexCategory.δ i)).f b ≫ _
  rw [cechLeftComponent_sum_f, cechLeftComponent_sum_f]
  simp only [HomologicalComplex.zsmul_f_apply, Preadditive.comp_sum,
    Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun k ↦ (-1 : ℤ) ^ (i : ℕ) • k)
    (CechAugmentedSquare.leftCι_naturality
      (schemePerfectCechTupleSquare_map f g F q hq U p hp hR hS (SimplexCategory.δ i)) b)

set_option backward.isDefEq.respectTransparency false in
/-- 元の基底の外零次の水平微分は、同じ恒等射の交代和により零。 -/
theorem schemePerfectCechTupleLeftBase_horizontal_zero :
    ((schemePerfectCechTupleSquareLeftPositiveDouble f g F q hq U p hp hR hS).d 0 1).f 0 = 0 := by
  change (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) •
    (schemePerfectCechTupleSquareLeftFunctor f g F q hq U p hp hR hS).map (SimplexCategory.δ i)).f 0 = 0
  rw [cechLeftComponent_sum_f]
  simp only [HomologicalComplex.zsmul_f_apply]
  change (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) •
    (𝟙 (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR)))) = 0
  simp [Fin.sum_univ_two]

end SerrePositivity.AlgebraicGeometry
