module
public import SerrePositivity.KST.SConstruction.DiagonalSInterchangeComponents

/-! # 固定 S 方向と全多次数の反復 S の交換
概要：対角に制限せず、独立な各次数を持つ反復 S の内外で S_m を交換する。
方針：二方向の交換を最内側から順に合成し、完全関手の自然同型として束ねる。
規約：全 gapped 図式を保つ。使われ方：各零方向の境界を交換で移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
attribute [local instance] CategoryTheory.endofunctorMonoidalCategory

/-- 任意の多次数の有限反復と固定 S_m の内外交換。 -/
def multiFixedSEndofunctorIso (m : ℕ) : (r : ℕ) →
    (d : Fin r → SimplexCategoryᵒᵖ) →
      sEndofunctor.{u} m ⋙ (multiSEndofunctor r).obj d ≅
        (multiSEndofunctor r).obj d ⋙ sEndofunctor m
  | 0, _ => Iso.refl _
  | r + 1, d =>
    Functor.isoWhiskerRight (multiFixedSEndofunctorIso m r (fun i => d i.succ))
      (sEndofunctor (d 0).unop.len) ≪≫
    Functor.isoWhiskerLeft ((multiSEndofunctor r).obj (fun i => d i.succ))
      (sInterchangeEndofunctorIso (d 0).unop.len m)

/-- 多次数交換の零回反復の成分は恒等射。 -/
lemma multiFixedSEndofunctorIso_zero_app (m : ℕ)
    (d : Fin 0 → SimplexCategoryᵒᵖ) (X : StableModel.{u}) :
    (multiFixedSEndofunctorIso m 0 d).hom.app X = 𝟙 (sStableModel m X) := rfl

/-- 多次数交換の次の成分は前の交換の像と最後の二方向交換の合成。 -/
lemma multiFixedSEndofunctorIso_succ_app (m r : ℕ)
    (d : Fin (r + 1) → SimplexCategoryᵒᵖ) (X : StableModel.{u}) :
    (multiFixedSEndofunctorIso m (r + 1) d).hom.app X =
      (sEndofunctor (d 0).unop.len).map
        ((multiFixedSEndofunctorIso m r (fun i => d i.succ)).hom.app X) ≫
      (sInterchangeStableIso (d 0).unop.len m
        (((multiSEndofunctor r).obj (fun i => d i.succ)).obj X)).hom := rfl

/-- 全多次数交換を対角へ制限すると、既存の反復交換の同じ成分を回収する。 -/
lemma multiFixedSEndofunctorIso_diagonal_app (m r : ℕ) (d : SimplexCategoryᵒᵖ)
    (X : StableModel.{u}) :
    (multiFixedSEndofunctorIso m r (fun _ => d)).hom.app X =
      ((diagonalFixedSInterchangeNatIso m r).hom.app d).app X := by
  induction r with
  | zero =>
    rw [multiFixedSEndofunctorIso_zero_app, diagonalFixedSInterchangeNatIso_zero_app]
  | succ r ih =>
    rw [multiFixedSEndofunctorIso_succ_app, diagonalFixedSInterchangeNatIso_succ_app, ih]
    rfl

end SerrePositivity.KST.SConstruction
