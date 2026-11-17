module

public import SerrePositivity.AlgebraicGeometry.AugmentedCechCoordinates

/-!
概要：元のnerveの最初の座標に沿うアフィンfppf細分を、合成の底変換へ送る。
方針：元のpullbackの二射影をそのままliftする。
規約：環・構造射・nerveの対象を変えず、射の性質も仮定しない。
使われ方：相対fppfの比較（承認済み計画F08・F09）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- 元の第一座標に沿うqの底変換から、同じq≫gの底変換への細分射。 -/
def fppfComparisonRefiner
    {R : Type u} [CommRing R] {A B : Scheme.{u}}
    (q : A ⟶ B) (g : B ⟶ Spec (CommRingCat.of R)) (n : SimplexCategory) :
    pullback q (WidePullback.π (fun _ : Fin (n.len+1) ↦ g) 0) ⟶
      pullback (q ≫ g) (augmentedNerveBase g (.of n)) :=
  pullback.lift (pullback.fst q (WidePullback.π (fun _ : Fin (n.len+1) ↦ g) 0))
    (pullback.snd q (WidePullback.π (fun _ : Fin (n.len+1) ↦ g) 0)) (by
      change pullback.fst q _ ≫ (q ≫ g) =
        pullback.snd q _ ≫ WidePullback.base (fun _ : Fin (n.len+1) ↦ g)
      rw [← Category.assoc, pullback.condition, Category.assoc, WidePullback.π_arrow])

/-- 同じ細分射は元のnerveへの射影を保持する。 -/
theorem fppfComparisonRefiner_over
    {R : Type u} [CommRing R] {A B : Scheme.{u}}
    (q : A ⟶ B) (g : B ⟶ Spec (CommRingCat.of R)) (n : SimplexCategory) :
    fppfComparisonRefiner q g n ≫ pullback.snd (q ≫ g) (augmentedNerveBase g (.of n)) =
      pullback.snd q (WidePullback.π (fun _ : Fin (n.len+1) ↦ g) 0) :=
  pullback.lift_snd _ _ _

end SerrePositivity.AlgebraicGeometry
