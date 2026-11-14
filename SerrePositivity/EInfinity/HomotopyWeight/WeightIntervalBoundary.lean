module
public import SerrePositivity.EInfinity.HomotopyWeight.WeightedSourceHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterHomotopy

/-!
概要：重みの同じ二つの射から区間境界の全自然な写像を作る。
方針：既存の境界の二成分の余極限と、その自然性を使う。
規約：IS-W2 R03a.1の境界持ち上げによる収縮の証明分割。
使われ方：元の重みの同じ切断を区間で恒等射へ結ぶ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.SimplicialModel.LargeParameterHomotopy
open scoped Simplicial

/-- 元の二つの射の境界の降下射は、同じ可換する二つの四角形で自然。 -/
theorem weight_boundaryMap_naturality {X Y E F : SSet.{u}} (r : X ⟶ Y) (t : E ⟶ F)
    (a b : X ⟶ E) (c d : Y ⟶ F) (ha : r ≫ c = a ≫ t) (hb : r ≫ d = b ≫ t) :
    (r ▷ (∂Δ[1] : SSet.{u})) ≫ boundaryMap c d = boundaryMap a b ≫ t := by
  apply (boundaryColimit X).hom_ext
  rintro ⟨j⟩
  cases j with
  | left =>
    change (X ◁ boundary.ι (1 : Fin 2)) ≫ (r ▷ (∂Δ[1] : SSet.{u})) ≫ boundaryMap c d =
      (X ◁ boundary.ι (1 : Fin 2)) ≫ boundaryMap a b ≫ t
    rw [whisker_exchange_assoc, boundaryMap_zero, boundaryMap_zero_assoc,
      whiskerRight_fst_assoc, ha]
  | right =>
    change (X ◁ boundary.ι (0 : Fin 2)) ≫ (r ▷ (∂Δ[1] : SSet.{u})) ≫ boundaryMap c d =
      (X ◁ boundary.ι (0 : Fin 2)) ≫ boundaryMap a b ≫ t
    rw [whisker_exchange_assoc, boundaryMap_one, boundaryMap_one_assoc,
      whiskerRight_fst_assoc, hb]

/-- 同じ基底への射が両端点で一致すれば、境界の貼り合わせも同じ一定の基底を保つ。 -/
theorem weight_boundaryMap_comp {X E B : SSet.{u}} (a b : X ⟶ E) (p : E ⟶ B)
    (h : a ≫ p = b ≫ p) :
    boundaryMap a b ≫ p = fst X (∂Δ[1] : SSet.{u}) ≫ b ≫ p := by
  apply (boundaryColimit X).hom_ext
  rintro ⟨j⟩
  cases j with
  | left =>
    change (X ◁ boundary.ι (1 : Fin 2)) ≫ boundaryMap a b ≫ p =
      (X ◁ boundary.ι (1 : Fin 2)) ≫ fst X _ ≫ b ≫ p
    rw [boundaryMap_zero_assoc, whiskerLeft_fst_assoc, h]
  | right =>
    change (X ◁ boundary.ι (0 : Fin 2)) ≫ boundaryMap a b ≫ p =
      (X ◁ boundary.ι (0 : Fin 2)) ≫ fst X _ ≫ b ≫ p
    rw [boundaryMap_one_assoc, whiskerLeft_fst_assoc]

variable (I : Type u) [SmallCategory I]

/-- 元の二つの全図式射の区間境界への同じ貼り合わせ。 -/
def weightIntervalBoundary {V W : I ⥤ SSet.{u}} (f g : V ⟶ W) :
    V ⊗ (Functor.const I).obj (∂Δ[1] : SSet.{u}) ⟶ W where
  app i := boundaryMap (f.app i) (g.app i)
  naturality i j h := weight_boundaryMap_naturality (V.map h) (W.map h)
    (f.app i) (g.app i) (f.app j) (g.app j) (f.naturality h) (g.naturality h)


/-- 同じ区間境界の持ち上げは、元のZero端点を保つ。 -/
theorem weightIntervalBoundary_lift_zero {V W : I ⥤ SSet.{u}} (f g : V ⟶ W)
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W)
    (h : (V ◁ (Functor.const I).map ∂Δ[1].ι) ≫ T = weightIntervalBoundary I f g) :
    weightIntervalZero I V ≫ T = f := by
  apply NatTrans.ext
  funext i
  have hi := NatTrans.congr_app h i
  change ((V.obj i) ◁ ∂Δ[1].ι) ≫ T.app i = boundaryMap (f.app i) (g.app i) at hi
  change SSet.ι₀ ≫ T.app i = f.app i
  rw [← section_zero (V.obj i), Category.assoc, ← boundary.ι_ι (1 : Fin 2),
    whiskerLeft_comp, Category.assoc, hi, boundaryMap_zero]
  rfl

/-- 同じ区間境界の持ち上げは、元のOne端点を保つ。 -/
theorem weightIntervalBoundary_lift_one {V W : I ⥤ SSet.{u}} (f g : V ⟶ W)
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W)
    (h : (V ◁ (Functor.const I).map ∂Δ[1].ι) ≫ T = weightIntervalBoundary I f g) :
    weightIntervalOne I V ≫ T = g := by
  apply NatTrans.ext
  funext i
  have hi := NatTrans.congr_app h i
  change ((V.obj i) ◁ ∂Δ[1].ι) ≫ T.app i = boundaryMap (f.app i) (g.app i) at hi
  change SSet.ι₁ ≫ T.app i = g.app i
  rw [← section_one (V.obj i), Category.assoc, ← boundary.ι_ι (0 : Fin 2),
    whiskerLeft_comp, Category.assoc, hi, boundaryMap_one]
  rfl

end SerrePositivity.EInfinity.HomotopyWeight
