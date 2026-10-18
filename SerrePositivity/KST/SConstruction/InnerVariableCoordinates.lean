module
public import SerrePositivity.KST.SConstruction.DiagonalIterationCoordinates

/-! # 最内側の次数を変数にした反復 S の座標
概要：外側の多次数を固定し、最内側の次数と作用素だけを動かす比較を作る。
方針：先頭の外側 S を方向数について順に付け足す。
規約：零次数の作用素も含む。使われ方：定数部分と最後の零方向との照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open scoped Simplicial

/-- 概要：外側 r 個の次数を固定し、最後の次数だけを変える添字関手。
方針：固定された先頭と、残りの添字への再帰を積関手で束ねる。
規約：追加する方向は最内側。使われ方：零方向の包含の座標。 -/
def innerVariableIndex (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ) :
    SimplexCategoryᵒᵖ ⥤ (Fin (r + 1) → SimplexCategoryᵒᵖ) := by
  induction r with
  | zero => exact Functor.pi' (fun _ => 𝟭 SimplexCategoryᵒᵖ)
  | succ r ih =>
    exact Functor.pi' (fun i => Fin.cases
      ((Functor.const SimplexCategoryᵒᵖ).obj (d 0))
      (fun j => ih (fun k => d k.succ) ⋙
        Pi.eval (fun _ : Fin (r + 1) => SimplexCategoryᵒᵖ) j) i)

/-- 概要：最内側の可変の S を外側の固定反復に入れた自己関手の座標同型。
方針：合成の右単位子と結合子で方向数について帰納する。
規約：安定な入力について自然。使われ方：最内側の零固定の比較。 -/
def innerVariableSComparisonIso (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    (k : SimplexCategoryᵒᵖ) :
    sEndofunctor.{u} k.unop.len ⋙ (multiSEndofunctor r).obj d ≅
      (multiSEndofunctor (r + 1)).obj ((innerVariableIndex r d).obj k) := by
  induction r with
  | zero => exact Functor.rightUnitor (sEndofunctor k.unop.len)
  | succ r ih =>
    change sEndofunctor k.unop.len ⋙
        ((multiSEndofunctor r).obj (fun i => d i.succ) ⋙ sEndofunctor (d 0).unop.len) ≅
      (multiSEndofunctor (r + 1)).obj
        ((innerVariableIndex r (fun i => d i.succ)).obj k) ⋙ sEndofunctor (d 0).unop.len
    exact (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ih (fun i => d i.succ)) (sEndofunctor (d 0).unop.len)

/-- 概要：最内側の作用素の外側への持ち上げは外側の自己関手への後合成。
方針：先頭の固定された作用は恒等であることを使う。
規約：自然変換の厳密等号。使われ方：可変の最内側の次数の自然性。 -/
lemma innerVariableSMap_succ (r : ℕ) (d : Fin (r + 1) → SimplexCategoryᵒᵖ)
    {k l : SimplexCategoryᵒᵖ} (f : k ⟶ l) :
    (multiSEndofunctor.{u} (r + 2)).map ((innerVariableIndex (r + 1) d).map f) =
      Functor.whiskerRight
        ((multiSEndofunctor (r + 1)).map ((innerVariableIndex r (fun i => d i.succ)).map f))
        (sEndofunctor (d 0).unop.len) := by
  apply NatTrans.ext
  funext X
  change ((simplicialStableEndofunctor.map (𝟙 (d 0))).app _) ≫
    (sEndofunctor (d 0).unop.len).map
    (((multiSEndofunctor (r + 1)).map
      ((innerVariableIndex r (fun i => d i.succ)).map f)).app X) = _
  rw [CategoryTheory.Functor.map_id]
  exact Category.id_comp _

/-- 概要：最内側の座標比較は零次数を含む全単体作用素について自然。
方針：方向数について帰納し、内側の自然性を外側の自己関手で写す。
規約：厳密な自然変換の等号。使われ方：定数方向の包含の比較。 -/
lemma innerVariableSComparisonIso_naturality (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    {k l : SimplexCategoryᵒᵖ} (f : k ⟶ l) :
    Functor.whiskerRight (simplicialStableEndofunctor.{u}.map f) ((multiSEndofunctor r).obj d) ≫
        (innerVariableSComparisonIso r d l).hom =
      (innerVariableSComparisonIso r d k).hom ≫
        (multiSEndofunctor (r + 1)).map ((innerVariableIndex r d).map f) := by
  induction r with
  | zero =>
    apply NatTrans.ext
    funext X
    change (simplicialStableEndofunctor.map f).app X ≫ 𝟙 _ =
      𝟙 _ ≫ ((simplicialStableEndofunctor.map f).app X ≫
        (simplicialStableEndofunctor.obj l).map (𝟙 X))
    simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  | succ r ih =>
    rw [innerVariableSMap_succ]
    apply NatTrans.ext
    funext X
    let F := sEndofunctor (d 0).unop.len
    have h := NatTrans.congr_app (ih (fun i => d i.succ)) X
    change F.map
        (((multiSEndofunctor r).obj (fun i => d i.succ)).map
          ((simplicialStableEndofunctor.map f).app X)) ≫
          F.map ((innerVariableSComparisonIso r (fun i => d i.succ) l).hom.app X) =
      F.map ((innerVariableSComparisonIso r (fun i => d i.succ) k).hom.app X) ≫
        F.map (((multiSEndofunctor (r + 1)).map
          ((innerVariableIndex r (fun i => d i.succ)).map f)).app X)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg F.map h

/-- 概要：追加した最後の方向は可変次数そのもの。
方針：外側の方向数について帰納する。
規約：外側の次数は任意。使われ方：最後の零方向の同定。 -/
lemma innerVariableIndex_obj_last (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    (k : SimplexCategoryᵒᵖ) : (innerVariableIndex r d).obj k (Fin.last r) = k := by
  induction r with
  | zero => rfl
  | succ r ih => exact ih (fun i => d i.succ)

/-- 概要：最後以外の方向は固定した外側の次数を保つ。
方針：方向数と有限添字について帰納する。
規約：元の添字は castSucc で保持。使われ方：零方向の補集合の同定。 -/
lemma innerVariableIndex_obj_castSucc (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    (k : SimplexCategoryᵒᵖ) (i : Fin r) :
    (innerVariableIndex r d).obj k i.castSucc = d i := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact ih (fun j => d j.succ) i

/-- 概要：最後の座標の作用は可変次数の作用素そのもの。
方針：方向数について帰納し、座標の同定を明示する。
規約：等号による輸送を両端に置く。使われ方：零方向の射の比較。 -/
lemma innerVariableIndex_map_last (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    {k l : SimplexCategoryᵒᵖ} (f : k ⟶ l) :
    eqToHom (innerVariableIndex_obj_last r d k).symm ≫
      ((innerVariableIndex r d).map f) (Fin.last r) ≫
      eqToHom (innerVariableIndex_obj_last r d l) = f := by
  induction r with
  | zero => exact Category.id_comp _ |>.trans (Category.comp_id _)
  | succ r ih => exact ih (fun i => d i.succ)

/-- 概要：外側の固定座標で可変次数の作用は恒等射。
方針：方向数と添字について帰納し、座標の同定を明示する。
規約：零方向の射も含む。使われ方：最後以外の方向の包含の比較。 -/
lemma innerVariableIndex_map_castSucc (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    {k l : SimplexCategoryᵒᵖ} (f : k ⟶ l) (i : Fin r) :
    eqToHom (innerVariableIndex_obj_castSucc r d k i).symm ≫
      ((innerVariableIndex r d).map f) i.castSucc ≫
      eqToHom (innerVariableIndex_obj_castSucc r d l i) = 𝟙 (d i) := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    cases i using Fin.cases with
    | zero => exact Category.id_comp _ |>.trans (Category.comp_id _)
    | succ i => exact ih (fun j => d j.succ) i

/-- 概要：可変の最内側の次数の座標比較を自然同型として束ねる。
方針：次数ごとの同型と証明済みの作用素についての自然性を使う。
規約：零次数を含む全単体圏。使われ方：零方向の包含との可換図式。 -/
def innerVariableSComparisonNatIso (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ) :
    simplicialStableEndofunctor.{u} ⋙
        (Functor.whiskeringRight StableModel.{u} StableModel.{u} StableModel.{u}).obj
          ((multiSEndofunctor r).obj d) ≅
      innerVariableIndex r d ⋙ multiSEndofunctor (r + 1) :=
  NatIso.ofComponents (innerVariableSComparisonIso r d)
    (fun f => innerVariableSComparisonIso_naturality r d f)

end SerrePositivity.KST.SConstruction
