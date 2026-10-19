module
public import SerrePositivity.KST.SConstruction.InnerVariableCoordinates

/-! # 最内側の添字を保つ外側全方向の作用
概要：最後の可変次数を保ち、外側の独立な各次数の作用を元の反復添字へ持ち上げる。
方針：固定した最後の座標の恒等射と外側の各射を再帰的に束ねる。
規約：元の innerVariableIndex の対象を使う。使われ方：座標の巡回移動と全零境界の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 最内側の可変次数を保ったまま、外側の全多次数の射を持ち上げる。 -/
def innerVariableOuterMap : (r : ℕ) →
    {d e : Fin r → SimplexCategoryᵒᵖ} → (d ⟶ e) → (k : SimplexCategoryᵒᵖ) →
      (innerVariableIndex r d).obj k ⟶ (innerVariableIndex r e).obj k
  | 0, _, _, _, k => fun _ => 𝟙 k
  | r + 1, _, _, f, k => fun i =>
    Fin.cases (f 0) (fun j => innerVariableOuterMap r (fun a => f a.succ) k j) i

/-- 外側の全方向の作用をさらに外側に延長する式。 -/
lemma innerVariableOuterMap_succ (r : ℕ)
    {d e : Fin (r + 1) → SimplexCategoryᵒᵖ} (f : d ⟶ e) (k : SimplexCategoryᵒᵖ)
    (X : StableModel.{u}) :
    ((multiSEndofunctor (r + 2)).map (innerVariableOuterMap (r + 1) f k)).app X =
      (simplicialStableEndofunctor.map (f 0)).app
        (((multiSEndofunctor (r + 1)).obj
          ((innerVariableIndex r (fun i => d i.succ)).obj k)).obj X) ≫
      (sEndofunctor (e 0).unop.len).map
        (((multiSEndofunctor (r + 1)).map
          (innerVariableOuterMap r (fun i => f i.succ) k)).app X) := rfl

/-- 外側の次数変更は元の最内側の座標比較と厳密に可換。 -/
lemma innerVariableSComparisonIso_outer_naturality (r : ℕ)
    {d e : Fin r → SimplexCategoryᵒᵖ} (f : d ⟶ e) (k : SimplexCategoryᵒᵖ)
    (X : StableModel.{u}) :
    ((multiSEndofunctor r).map f).app (sStableModel k.unop.len X) ≫
        (innerVariableSComparisonIso r e k).hom.app X =
      (innerVariableSComparisonIso r d k).hom.app X ≫
        ((multiSEndofunctor (r + 1)).map (innerVariableOuterMap r f k)).app X := by
  induction r with
  | zero =>
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫
      ((simplicialStableEndofunctor.map (𝟙 k)).app X ≫
        (sEndofunctor k.unop.len).map (𝟙 X))
    rw [CategoryTheory.Functor.map_id]
    simp only [NatTrans.id_app, CategoryTheory.Functor.map_id, Category.comp_id,
      Category.id_comp]
    rfl
  | succ r ih =>
    let F := sEndofunctor (d 0).unop.len
    let G := sEndofunctor (e 0).unop.len
    let a := simplicialStableEndofunctor.map (f 0)
    let D := (multiSEndofunctor r).obj (fun i => d i.succ)
    let b := (innerVariableSComparisonIso r (fun i => d i.succ) k).hom.app X
    have ht := ih (fun i => f i.succ)
    have ha : a.app (D.obj (sStableModel k.unop.len X)) ≫ G.map b =
        F.map b ≫ a.app
          (((multiSEndofunctor (r + 1)).obj
            ((innerVariableIndex r (fun i => d i.succ)).obj k)).obj X) :=
      (a.naturality b).symm
    rw [innerVariableOuterMap_succ]
    change (a.app (D.obj (sStableModel k.unop.len X)) ≫
      G.map (((multiSEndofunctor r).map (fun i => f i.succ)).app
        (sStableModel k.unop.len X))) ≫
      (𝟙 _ ≫ G.map ((innerVariableSComparisonIso r (fun i => e i.succ) k).hom.app X)) =
      (𝟙 _ ≫ F.map b) ≫ _
    simp only [Category.id_comp]
    rw [Category.assoc, ← G.map_comp, ht, G.map_comp,
      ← Category.assoc, ha, Category.assoc]

end SerrePositivity.KST.SConstruction
