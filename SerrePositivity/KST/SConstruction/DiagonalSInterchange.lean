module
public import SerrePositivity.KST.SConstruction.SInterchangeEvaluations
public import SerrePositivity.KST.SConstruction.DiagonalIterationNaturality

/-! # 一つの S_m と対角有限反復の自然な交換
概要：固定した S_m を有限反復 S の最内側から最外側へ自然な厳密同型で移す。
方針：一方向の交換を単体的自己関手の自然同型へ束ね、結合子を使い反復数で帰納する。
規約：次数と安定な入力の両方について自然。使われ方：経路零行と構造射の源の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
attribute [local instance] CategoryTheory.endofunctorMonoidalCategory

/-- 一つの固定した S_m と単体的 S• の全単体的な自然な交換同型。 -/
def simplicialFixedSInterchangeNatIso (m : ℕ) :
    ((Functor.const SimplexCategoryᵒᵖ).obj (sEndofunctor.{u} m)) ⊗ simplicialStableEndofunctor ≅
      simplicialStableEndofunctor ⊗ ((Functor.const SimplexCategoryᵒᵖ).obj (sEndofunctor m)) :=
  NatIso.ofComponents (fun d => sInterchangeEndofunctorIso d.unop.len m) (by
    intro d e f
    apply NatTrans.ext
    funext X
    change (((𝟙 (sEndofunctor m) ⊗ₘ simplicialStableEndofunctor.map f) ≫
      (sInterchangeEndofunctorIso e.unop.len m).hom).app X) =
      (((sInterchangeEndofunctorIso d.unop.len m).hom ≫
        (simplicialStableEndofunctor.map f ⊗ₘ 𝟙 (sEndofunctor m))).app X)
    simp only [NatTrans.comp_app, endofunctorMonoidalCategory_tensorMap_app,
      NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    apply Subtype.ext
    change sMap (sConstruction m X.carrier) f.unop.toOrderHom ≫
      sInterchange e.unop.len m X.carrier =
      sInterchange d.unop.len m X.carrier ≫
        ((sEndofunctor m).map ((sEndofunctorMap f.unop.toOrderHom).app X)).val
    exact sInterchange_outerMap m X f.unop.toOrderHom)

/-- 固定した S_m は対角有限反復 S の最内側から最外側へ自然な厳密同型で移る。 -/
def diagonalFixedSInterchangeNatIso (m r : ℕ) :
    ((Functor.const SimplexCategoryᵒᵖ).obj (sEndofunctor.{u} m)) ⊗ diagonalSEndofunctor r ≅
      diagonalSEndofunctor r ⊗ ((Functor.const SimplexCategoryᵒᵖ).obj (sEndofunctor m)) := by
  let T := (Functor.const SimplexCategoryᵒᵖ).obj (sEndofunctor.{u} m)
  induction r with
  | zero =>
    exact eqToIso (congrArg (fun F => T ⊗ F) diagonalSEndofunctor_zero) ≪≫
      (ρ_ T) ≪≫ (λ_ T).symm ≪≫
      (eqToIso (congrArg (fun F => F ⊗ T) diagonalSEndofunctor_zero)).symm
  | succ r ih =>
    exact eqToIso (congrArg (fun F => T ⊗ F) (diagonalSEndofunctor_succ r)) ≪≫
      (α_ _ _ _).symm ≪≫ whiskerRightIso ih simplicialStableEndofunctor ≪≫
      (α_ _ _ _) ≪≫ whiskerLeftIso (diagonalSEndofunctor r)
        (simplicialFixedSInterchangeNatIso m) ≪≫
      (α_ _ _ _).symm ≪≫
      (eqToIso (congrArg (fun F => F ⊗ T) (diagonalSEndofunctor_succ r))).symm

end SerrePositivity.KST.SConstruction
