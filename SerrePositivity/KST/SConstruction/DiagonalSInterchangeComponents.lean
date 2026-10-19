module
public import SerrePositivity.KST.SConstruction.DiagonalSInterchange

/-! # 固定 S 方向の有限反復交換の成分と S₁ 評価
概要：反復交換の成分の再帰式を示し、最外側の元の S₁ 比較が最内側の S₁ 比較を回収すると証明する。
方針：結合子の成分と二方向の交換・評価の厳密な式を反復数で帰納する。
規約：自然同型を別の成分で置換しない。使われ方：二つの前段比較の厳密な照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
attribute [local instance] CategoryTheory.endofunctorMonoidalCategory

/-- 零回反復の固定 S 交換の成分は恒等射。 -/
lemma diagonalFixedSInterchangeNatIso_zero_app (m : ℕ) (d : SimplexCategoryᵒᵖ)
    (X : StableModel.{u}) :
    ((diagonalFixedSInterchangeNatIso m 0).hom.app d).app X = 𝟙 (sStableModel m X) := by
  simp [diagonalFixedSInterchangeNatIso, Nat.recAux, diagonalSEndofunctor,
    multiSEndofunctor, multiIndexDiagonal]
  rfl

/-- 次の反復の固定 S 交換は前の交換の像と最後の二方向の交換の合成。 -/
lemma diagonalFixedSInterchangeNatIso_succ_app (m r : ℕ) (d : SimplexCategoryᵒᵖ)
    (X : StableModel.{u}) :
    ((diagonalFixedSInterchangeNatIso m (r + 1)).hom.app d).app X =
      (sEndofunctor d.unop.len).map (((diagonalFixedSInterchangeNatIso m r).hom.app d).app X) ≫
        (sInterchangeStableIso d.unop.len m (((diagonalSEndofunctor r).obj d).obj X)).hom := by
  simp only [diagonalSEndofunctor, multiIndexDiagonal, multiSEndofunctor,
    Monoidal.tensorObj_obj, Functor.const_obj_obj, Functor.comp_obj, Functor.prod'_obj,
    Functor.uncurry_obj_obj, Functor.whiskeringRight_obj_obj,
    endofunctorMonoidalCategory_tensorObj_obj, diagonalFixedSInterchangeNatIso,
    Nat.recAux, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, simplicialFixedSInterchangeNatIso,
    sInterchangeEndofunctorIso, Iso.trans_hom, eqToIso.hom, Iso.symm_hom,
    whiskerRightIso_hom, whiskerLeftIso_hom, eqToIso.inv, NatTrans.comp_app,
    eqToHom_app, eqToHom_refl, Monoidal.associator_inv_app, Monoidal.whiskerRight_app,
    Monoidal.associator_hom_app, Monoidal.whiskerLeft_app, NatIso.ofComponents_hom_app,
    Category.comp_id, Category.id_comp, endofunctorMonoidalCategory_associator_inv_app,
    endofunctorMonoidalCategory_whiskerRight_app, endofunctorMonoidalCategory_associator_hom_app,
    endofunctorMonoidalCategory_whiskerLeft_app]
  exact Category.id_comp _

/-- 交換後の最外側の S₁ 比較は元の入力の S₁ 比較への後合成そのもの。 -/
lemma sInterchangeStableIso_sOneComparison_right (n : ℕ) (X : StableModel.{u}) :
    (sInterchangeStableIso n 1 X).hom ≫ stableSOneComparison (sStableModel n X) =
      (sEndofunctor n).map (stableSOneComparison X) := by
  have hi : (sInterchangeStableIso n 1 X).hom ≫ (sInterchangeStableIso 1 n X).hom = 𝟙 _ :=
    Subtype.ext (sInterchange_twice n 1 X.carrier)
  rw [← sInterchangeStableIso_sOneComparison, ← Category.assoc, hi, Category.id_comp]

/-- 有限反復の内外交換の後の元の S₁ 比較は内側の S₁ 比較への反復関手の作用を回収する。 -/
lemma diagonalFixedSInterchangeNatIso_sOneComparison (r : ℕ) (d : SimplexCategoryᵒᵖ)
    (X : StableModel.{u}) :
    ((diagonalFixedSInterchangeNatIso 1 r).hom.app d).app X ≫
        stableSOneComparison (((diagonalSEndofunctor r).obj d).obj X) =
      ((diagonalSEndofunctor r).obj d).map (stableSOneComparison X) := by
  induction r with
  | zero =>
    rw [diagonalFixedSInterchangeNatIso_zero_app]
    change 𝟙 (sStableModel 1 X) ≫ stableSOneComparison X = stableSOneComparison X
    exact Category.id_comp _
  | succ r ih =>
    rw [diagonalFixedSInterchangeNatIso_succ_app]
    change ((sEndofunctor d.unop.len).map
      (((diagonalFixedSInterchangeNatIso 1 r).hom.app d).app X) ≫
        (sInterchangeStableIso d.unop.len 1 (((diagonalSEndofunctor r).obj d).obj X)).hom) ≫
      stableSOneComparison (sStableModel d.unop.len (((diagonalSEndofunctor r).obj d).obj X)) =
        (sEndofunctor d.unop.len).map
          (((diagonalSEndofunctor r).obj d).map (stableSOneComparison X))
    rw [Category.assoc, sInterchangeStableIso_sOneComparison_right,
      ← CategoryTheory.Functor.map_comp, ih]

end SerrePositivity.KST.SConstruction
