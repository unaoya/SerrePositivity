module

public import SerrePositivity.AlgebraicGeometry.SchemeVCoverComposition
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
概要：affine tensor 模型と固有模型の二つの Cartesian な底変換を接続する。
方針：実際の pullback の普遍性と、二つの pullback square の貼り合わせを使う。
規約：Rydh Proposition 3.7。v 判定の底変換は既存の API を使う。
使われ方：閉包絡へ渡す周辺空間の v 判定を元の射から供給する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {X X₀ S S₀ Y Y₀ : Scheme.{u}}
  {a : X ⟶ X₀} {x : X ⟶ S} {f₀ : X₀ ⟶ S₀} {g : S ⟶ S₀}
  {v : Y ⟶ Y₀} {p : Y ⟶ S} {p₀ : Y₀ ⟶ S₀}

private theorem iteratedModelBaseChange_comm
    (hY : IsPullback v p p₀ g) :
    (pullback.fst (pullback.snd f₀ p₀) v ≫ pullback.fst f₀ p₀) ≫ f₀ =
      (pullback.snd (pullback.snd f₀ p₀) v ≫ p) ≫ g := by
  calc
    _ = pullback.fst (pullback.snd f₀ p₀) v ≫ (pullback.snd f₀ p₀ ≫ p₀) := by
      rw [Category.assoc, pullback.condition]
    _ = (pullback.snd (pullback.snd f₀ p₀) v ≫ v) ≫ p₀ := by
      rw [← Category.assoc, pullback.condition]
    _ = _ := by rw [Category.assoc, hY.w, ← Category.assoc]

/-- 元の tensor 模型に、固有模型の底変換の周辺空間から戻す実際の射。 -/
def iteratedModelBaseChangeMap (hX : IsPullback a x f₀ g) (hY : IsPullback v p p₀ g) :
    pullback (pullback.snd f₀ p₀) v ⟶ X :=
  hX.lift (pullback.fst (pullback.snd f₀ p₀) v ≫ pullback.fst f₀ p₀)
    (pullback.snd (pullback.snd f₀ p₀) v ≫ p) (by exact iteratedModelBaseChange_comm hY)

@[reassoc (attr := simp)]
theorem iteratedModelBaseChangeMap_fst
    (hX : IsPullback a x f₀ g) (hY : IsPullback v p p₀ g) :
    iteratedModelBaseChangeMap hX hY ≫ a =
      pullback.fst (pullback.snd f₀ p₀) v ≫ pullback.fst f₀ p₀ := by
  simp [iteratedModelBaseChangeMap]

@[reassoc (attr := simp)]
theorem iteratedModelBaseChangeMap_base
    (hX : IsPullback a x f₀ g) (hY : IsPullback v p p₀ g) :
    iteratedModelBaseChangeMap hX hY ≫ x = pullback.snd (pullback.snd f₀ p₀) v ≫ p := by
  simp [iteratedModelBaseChangeMap]

/-- 同じ実際の射と第二射影は、元の射の底変換を与える。 -/
theorem isPullback_iteratedModelBaseChangeMap
    (hX : IsPullback a x f₀ g) (hY : IsPullback v p p₀ g) :
    IsPullback (iteratedModelBaseChangeMap hX hY) (pullback.snd (pullback.snd f₀ p₀) v) x p := by
  have houter : IsPullback
      (iteratedModelBaseChangeMap hX hY ≫ a)
      (pullback.snd (pullback.snd f₀ p₀) v) f₀ (p ≫ g) := by
    rw [iteratedModelBaseChangeMap_fst, ← hY.w]
    exact ((IsPullback.of_hasPullback (pullback.snd f₀ p₀) v).flip.paste_vert
      (IsPullback.of_hasPullback f₀ p₀).flip).flip
  exact houter.of_right (iteratedModelBaseChangeMap_base hX hY) hX

/-- 元の v 判定を、底変換した模型の周辺空間の第二射影へ渡す。 -/
theorem isSchemeVCover_iteratedModelBaseChange
    (hX : IsPullback a x f₀ g) (hY : IsPullback v p p₀ g) (hx : IsSchemeVCover x) :
    IsSchemeVCover (pullback.snd (pullback.snd f₀ p₀) v) :=
  IsSchemeVCover.baseChange (isPullback_iteratedModelBaseChangeMap hX hY) hx

end SerrePositivity.AlgebraicGeometry
