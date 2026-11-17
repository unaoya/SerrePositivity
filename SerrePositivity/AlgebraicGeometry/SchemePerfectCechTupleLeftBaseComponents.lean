module

public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareLeftComponents
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleSquarePositiveBaseLeftRight

/-!
概要：元のY側の基底射影の、同じ零次と正次数の成分。
方針：元のCの座標の同型と実際のpositiveBaseLeftProjectionの定義を使う。
規約：元のkernelに用いた射影そのものを計算する。
使われ方：同じtotalの分裂の第二式と合成零の照合。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u v

/-- 元のCの座標の包含と射影を、同じ二つの合成の式で同型へまとめる。 -/
def CechAugmentedSquare.leftCIso {A : Type v} [CommRing A]
    (s : CechAugmentedSquare.{u} A) (b : ℕ) :
    s.C.X b ≅ s.leftSquare.totalComplex.X (b + 1) where
  hom := s.leftCι b
  inv := s.leftCπ b
  hom_inv_id := s.leftCι_π b
  inv_hom_id := s.leftCπ_ι b

set_option backward.isDefEq.respectTransparency false in
/-- 元のY側の正の縦次数は、同じ基底射影で零に写る。 -/
theorem CechAugmentedSquare.baseProjection_onLeft_f_succ_zero
    {A : Type v} [CommRing A] (s : CechAugmentedSquare.{u} A) (b : ℕ) :
    ((CechAugmentedSquare.Map.baseProjection s).onLeftSquare.totalComplexMap).f (b + 1) = 0 := by
  apply (cancel_epi (s.leftCIso b).hom).mp
  simpa only [CechAugmentedSquare.leftCIso, comp_zero] using s.leftCι_baseProjection b

variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 元の正次数への基底射影の外零次は、全ての縦次数で零。 -/
theorem schemePerfectCechTupleLeftBaseProjection_zero (b : ℕ) :
    ((schemePerfectCechTupleSquarePositiveBaseLeftProjection f g F q hq U p hp hR hS).f 0).f b = 0 := by
  change _ ≫ (0 : _ ⟶ _) = 0
  exact comp_zero

set_option backward.isDefEq.respectTransparency false in
/-- 元の基底射影は正の外次数の正の縦次数でも零。 -/
theorem schemePerfectCechTupleLeftBaseProjection_succ_succ (a b : ℕ) :
    ((schemePerfectCechTupleSquarePositiveBaseLeftProjection f g F q hq U p hp hR hS).f
      (a + 1)).f (b + 1) = 0 := by
  change ((CechAugmentedSquare.Map.baseProjection
    (schemePerfectCechTupleSquare f g F q hq U p hp hR hS (SimplexCategory.mk (a + 1)))).onLeftSquare.totalComplexMap).f
      (b + 1) ≫ 𝟙 _ = 0
  rw [Category.comp_id]
  exact CechAugmentedSquare.baseProjection_onLeft_f_succ_zero _ b

set_option backward.isDefEq.respectTransparency false in
/-- 元の基底射影の正の外次数・縦零次は同じRの恒等射。 -/
theorem schemePerfectCechTupleLeftBaseProjection_succ_zero (a : ℕ) :
    ((schemePerfectCechTupleSquarePositiveBaseLeftProjection f g F q hq U p hp hR hS).f
      (a + 1)).f 0 = 𝟙 (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR)) := by
  rfl

end SerrePositivity.AlgebraicGeometry
