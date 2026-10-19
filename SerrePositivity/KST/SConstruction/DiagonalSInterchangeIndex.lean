module
public import SerrePositivity.KST.SConstruction.DiagonalSInterchangeComponents

/-! # 有限反復 S の交換の固定方向に関する自然性
概要：固定した S_m の次数を変える全ての面・退化は、内外交換と厳密に可換。
方針：交換成分の再帰式と二方向交換の内側の自然性を反復数で帰納する。
規約：元の自然同型の成分を保つ。使われ方：区間族を内側から外側へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
attribute [local instance] CategoryTheory.endofunctorMonoidalCategory

/-- 固定方向の全順序写像は、有限反復の内外交換と厳密に可換。 -/
lemma diagonalFixedSInterchangeNatIso_index {m m' : ℕ} (r : ℕ)
    (d : SimplexCategoryᵒᵖ) (X : StableModel.{u})
    (θ : Fin (m' + 1) →o Fin (m + 1)) :
    ((diagonalSEndofunctor r).obj d).map ((sEndofunctorMap θ).app X) ≫
        ((diagonalFixedSInterchangeNatIso m' r).hom.app d).app X =
      ((diagonalFixedSInterchangeNatIso m r).hom.app d).app X ≫
        (sEndofunctorMap θ).app (((diagonalSEndofunctor r).obj d).obj X) := by
  induction r with
  | zero =>
    rw [diagonalFixedSInterchangeNatIso_zero_app, diagonalFixedSInterchangeNatIso_zero_app]
    change (sEndofunctorMap θ).app X ≫ 𝟙 _ = 𝟙 _ ≫ (sEndofunctorMap θ).app X
    rw [Category.comp_id, Category.id_comp]
  | succ r ih =>
    rw [diagonalFixedSInterchangeNatIso_succ_app, diagonalFixedSInterchangeNatIso_succ_app]
    let F := sEndofunctor d.unop.len
    let Y := ((diagonalSEndofunctor r).obj d).obj X
    have hn : F.map ((sEndofunctorMap θ).app Y) ≫
        (sInterchangeStableIso d.unop.len m' Y).hom =
      (sInterchangeStableIso d.unop.len m Y).hom ≫
        (sEndofunctorMap θ).app (F.obj Y) :=
      Subtype.ext (sInterchange_innerMap d.unop.len Y θ)
    change F.map (((diagonalSEndofunctor r).obj d).map ((sEndofunctorMap θ).app X)) ≫
      (F.map (((diagonalFixedSInterchangeNatIso m' r).hom.app d).app X) ≫
        (sInterchangeStableIso d.unop.len m' Y).hom) =
      (F.map (((diagonalFixedSInterchangeNatIso m r).hom.app d).app X) ≫
        (sInterchangeStableIso d.unop.len m Y).hom) ≫
          (sEndofunctorMap θ).app (F.obj Y)
    rw [← Category.assoc, ← F.map_comp, ih, F.map_comp, Category.assoc, hn,
      Category.assoc]

end SerrePositivity.KST.SConstruction
