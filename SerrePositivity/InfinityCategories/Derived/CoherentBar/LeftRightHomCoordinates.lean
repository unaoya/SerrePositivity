module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.LeftRightHomIso
/-!
概要：左右 pinched Hom の厳密同型の全線形成分を計算する。
方針：反対模型の座標、線形反転、恒等 Hom 鎖写像の実計算則を合成する。
規約：全非空部分集合・全次数を保持する。
使われ方：標準 native 余錐の族との単体ごとの照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] (x y : C)

lemma dgCoherentBarLeftRightHomIso_linear {n : ℕ}
    (s : (pinchedHomLeft (X := dgNerve R C) (Simplex.vertex x) (Simplex.vertex y)) _⦋n⦌) :
    toLinearSimplex ((dgCoherentBarLeftRightHomIso R C x y).hom.app (Opposite.op ⦋n⦌) s) =
      pinchedLinearSimplexMap (A := R) (D := Cᵒᵖ) (E := C)
        (x := Opposite.op y) (y := Opposite.op x) (x' := x) (y' := y)
        (𝟙 (homObject R C x y))
        (dgCoherentBarLinearReflectionSimplex (dgLeftPinchedLinearEquiv R C x y n s)) := by
  change toLinearSimplex (pinchedHomChainMapSimplex (A := R) (D := Cᵒᵖ) (E := C)
    (x := Opposite.op y) (y := Opposite.op x) (x' := x) (y' := y)
    (𝟙 (homObject R C x y))
    (dgCoherentBarPinchedReflectionSimplex R Cᵒᵖ (Opposite.op y) (Opposite.op x)
      (SSet.opObjEquiv ((dgLeftPinchedOppositeIso R C x y).hom.app _ s)))) = _
  rw [pinchedHomChainMapSimplex_linear, dgCoherentBarPinchedReflectionSimplex_linear]
  rfl

lemma dgCoherentBarLeftRightHomIso_component {n : ℕ}
    (s : (pinchedHomLeft (X := dgNerve R C) (Simplex.vertex x) (Simplex.vertex y)) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    HEq ((toLinearData
      ((dgCoherentBarLeftRightHomIso R C x y).hom.app (Opposite.op ⦋n⦌) s)).component J k hJ hk)
      (dgCoherentBarLinearReflectionSign J.card •
        (dgLeftPinchedLinearEquiv R C x y n s).val.component
          (DGNerveOppositeIndex.reverse J) k (hJ.image Fin.rev)
          (by simpa only [DGNerveOppositeIndex.card_reverse] using hk)) := by
  have h := congrArg Subtype.val (dgCoherentBarLeftRightHomIso_linear R C x y s)
  change toLinearData _ = _ at h
  rw [h]
  rfl

end SerrePositivity.InfinityCategories
