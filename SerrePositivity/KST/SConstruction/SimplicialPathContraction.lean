module
public import SerrePositivity.KST.SConstruction.SimplicialPath
public import SerrePositivity.KST.SConstruction.DiagonalReduction
public import SerrePositivity.CategoryTheory.Simplex.Prefix

/-! # 経路構成の対角の実際の収縮
概要：経路構成の対角は元の零段へ区間ホモトピーで変形収縮する。
方針：先頭頂点を固定し、区間の単体に沿って残りの頂点を先頭へ移す。
規約：対角の Kan 性を要求しない。使われ方：S の経路実現の弱可縮性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

/-- 概要：区間パラメータで先頭以外の頂点を先頭へ移す単調自己写像。
方針：先頭は零、後続頂点は cut の値とする。
規約：区間零で定数、区間一で恒等。使われ方：経路実現の cylinder 写像。 -/
def simplicialPathCut (d : SimplexCategory) (t : (Δ[1] : SSet.{u}).obj (Opposite.op d)) :
    SimplexPrefix.functor.obj d ⟶ SimplexPrefix.functor.obj d :=
  SimplexCategory.Hom.mk ⟨Fin.cases 0 (SimplexPrefix.cut d t).toOrderHom, by
    intro i j hij
    induction i using Fin.cases with
    | zero => exact Fin.zero_le _
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        exact (SimplexPrefix.cut d t).toOrderHom.monotone (Fin.succ_le_succ_iff.mp hij)⟩

/-- 概要：頂点を先頭へ移す自己写像は全単体作用素と両立。
方針：先頭と後続頂点に分け、cut の自然性と区間の条件分岐を計算する。
規約：厳密等号。使われ方：cylinder 写像の自然性。 -/
lemma simplicialPathCut_naturality {d e : SimplexCategory} (f : d ⟶ e)
    (t : (Δ[1] : SSet.{u}).obj (Opposite.op e)) :
    SimplexPrefix.functor.map f ≫ simplicialPathCut e t =
      simplicialPathCut d ((Δ[1] : SSet.{u}).map f.op t) ≫ SimplexPrefix.functor.map f := by
  ext j : 3
  induction j using Fin.cases with
  | zero => rfl
  | succ j =>
    change (if (stdSimplex.objEquiv t).toOrderHom (f.toOrderHom j) = 0 then 0
        else (f.toOrderHom j).succ) =
      Fin.cases 0 (fun i => (f.toOrderHom i).succ)
        (if (stdSimplex.objEquiv t).toOrderHom (f.toOrderHom j) = 0 then 0 else j.succ)
    split_ifs <;> rfl

/-- 概要：区間零での自己写像は先頭頂点への定数写像。
方針：各頂点で零になることを計算する。
規約：始点は HA の endpoint 零。使われ方：収縮の始点。 -/
lemma simplicialPathCut_zero (d : SimplexCategory) :
    simplicialPathCut d (SimplexPrefix.endpoint.{u} d 0) =
      SimplexCategory.isTerminalZero.from (SimplexPrefix.functor.obj d) ≫
        simplicialPathVertex d := by
  ext j : 3
  induction j using Fin.cases with
  | zero => rfl
  | succ j =>
    change (SimplexPrefix.cut d (SimplexPrefix.endpoint.{u} d 0)).toOrderHom j = 0
    rw [SimplexPrefix.cut_zero]
    rfl

/-- 概要：区間一での自己写像は恒等写像。
方針：各後続頂点で cut_one の式を使う。
規約：終点は HA の endpoint 一。使われ方：収縮の終点。 -/
lemma simplicialPathCut_one (d : SimplexCategory) :
    simplicialPathCut d (SimplexPrefix.endpoint.{u} d 1) = 𝟙 (SimplexPrefix.functor.obj d) := by
  ext j : 3
  induction j using Fin.cases with
  | zero => rfl
  | succ j =>
    change (SimplexPrefix.cut d (SimplexPrefix.endpoint.{u} d 1)).toOrderHom j = j.succ
    rw [SimplexPrefix.cut_one]
    exact Fin.succAbove_zero_apply j

/-- 概要：元の零段から経路構成への定数経路の単体的切断。
方針：全頂点を唯一の零段へ送る単体作用素で引き戻す。
規約：選択は不要。使われ方：経路実現の変形収縮。 -/
def simplicialPathSection (X : SimplicialObject SSet.{u}) :
    (Functor.const SimplexCategoryᵒᵖ).obj (X.obj (Opposite.op ⦋0⦌)) ⟶ simplicialPath X where
  app d := X.map (SimplexCategory.isTerminalZero.from (SimplexPrefix.functor.obj d.unop)).op
  naturality {d e} f := by
    change 𝟙 _ ≫ X.map (SimplexCategory.isTerminalZero.from (SimplexPrefix.functor.obj e.unop)).op =
      X.map (SimplexCategory.isTerminalZero.from (SimplexPrefix.functor.obj d.unop)).op ≫
        X.map (SimplexPrefix.functor.map f.unop).op
    rw [Category.id_comp, ← X.map_comp, ← op_comp]
    congr 2

/-- 概要：経路構成の対角から元の零段への射影。
方針：augmentation を対角で評価する。
規約：標的は元の零段そのもの。使われ方：経路実現の比較。 -/
def simplicialPathDiagonalProjection (X : SimplicialObject SSet.{u}) :
    simplicialDiagonalFunctor.obj (simplicialPath X) ⟶ X.obj (Opposite.op ⦋0⦌) :=
  simplicialDiagonalFunctor.map (simplicialPathAugmentation X)

/-- 概要：零段から経路実現への定数経路の切断。
方針：単体的な切断を対角で評価する。
規約：選択なし。使われ方：収縮の定数部分。 -/
def simplicialPathDiagonalSection (X : SimplicialObject SSet.{u}) :
    X.obj (Opposite.op ⦋0⦌) ⟶ simplicialDiagonalFunctor.obj (simplicialPath X) :=
  simplicialDiagonalFunctor.map (simplicialPathSection X)

/-- 概要：経路実現の自己写像の実際の cylinder。
方針：区間の単体が指定する単調自己写像で元の図式を引き戻す。
規約：先頭頂点を固定する。使われ方：変形収縮のホモトピー。 -/
def simplicialPathDiagonalCylinder (X : SimplicialObject SSet.{u}) :
    simplicialDiagonalFunctor.obj (simplicialPath X) ⊗ (Δ[1] : SSet.{u}) ⟶
      simplicialDiagonalFunctor.obj (simplicialPath X) where
  app d := ↾fun z => (X.map (simplicialPathCut d.unop z.2).op).app d z.1
  naturality {d e} f := by
    apply ConcreteCategory.hom_ext
    intro z
    change (X.map (simplicialPathCut e.unop ((Δ[1] : SSet.{u}).map f z.2)).op).app e
        (((X.obj (Opposite.op (SimplexPrefix.functor.obj e.unop))).map f)
          ((X.map (SimplexPrefix.functor.map f.unop).op).app d z.1)) =
      ((X.obj (Opposite.op (SimplexPrefix.functor.obj e.unop))).map f)
        ((X.map (SimplexPrefix.functor.map f.unop).op).app d
          ((X.map (simplicialPathCut d.unop z.2).op).app d z.1))
    refine (ConcreteCategory.congr_hom
      ((X.map (simplicialPathCut e.unop ((Δ[1] : SSet.{u}).map f z.2)).op).naturality f)
        ((X.map (SimplexPrefix.functor.map f.unop).op).app d z.1)).trans ?_
    apply congrArg ((X.obj (Opposite.op (SimplexPrefix.functor.obj e.unop))).map f)
    change (X.map (SimplexPrefix.functor.map f.unop).op ≫
        X.map (simplicialPathCut e.unop ((Δ[1] : SSet.{u}).map f z.2)).op).app d z.1 =
      (X.map (simplicialPathCut d.unop z.2).op ≫
        X.map (SimplexPrefix.functor.map f.unop).op).app d z.1
    rw [← X.map_comp, ← X.map_comp, ← op_comp, ← op_comp]
    exact congrArg (fun k => (X.map k.op).app d z.1)
      (simplicialPathCut_naturality f.unop z.2).symm

/-- 概要：定数経路の切断の後で射影すると元の零段を厳密に回収する。
方針：零段の自己射の一意性と図式の合成法則を使う。
規約：厳密等号。使われ方：変形収縮の切断条件。 -/
lemma simplicialPathDiagonalSection_projection (X : SimplicialObject SSet.{u}) :
    simplicialPathDiagonalSection X ≫ simplicialPathDiagonalProjection X = 𝟙 _ := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  change (X.map (SimplexCategory.isTerminalZero.from (SimplexPrefix.functor.obj d.unop)).op ≫
    X.map (simplicialPathVertex d.unop).op).app d z = z
  rw [← X.map_comp, ← op_comp]
  have he : simplicialPathVertex d.unop ≫
      SimplexCategory.isTerminalZero.from (SimplexPrefix.functor.obj d.unop) = 𝟙 ⦋0⦌ :=
    Subsingleton.elim _ _
  rw [he, op_id, X.map_id]
  rfl

/-- 概要：経路実現の cylinder の始点は射影と定数切断の合成。
方針：区間零での頂点の自己写像の式を使う。
規約：始点は ι₀。使われ方：変形収縮の始点。 -/
lemma simplicialPathDiagonalCylinder_zero (X : SimplicialObject SSet.{u}) :
    SSet.ι₀ ≫ simplicialPathDiagonalCylinder X =
      simplicialPathDiagonalProjection X ≫ simplicialPathDiagonalSection X := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  change (X.map (simplicialPathCut d.unop (SimplexPrefix.endpoint.{u} d.unop 0)).op).app d z =
    (X.map (simplicialPathVertex d.unop).op ≫
      X.map (SimplexCategory.isTerminalZero.from (SimplexPrefix.functor.obj d.unop)).op).app d z
  rw [simplicialPathCut_zero, op_comp, X.map_comp]

/-- 概要：経路実現の cylinder の終点は恒等射。
方針：区間一での頂点の自己写像の式を使う。
規約：終点は ι₁。使われ方：変形収縮の終点。 -/
lemma simplicialPathDiagonalCylinder_one (X : SimplicialObject SSet.{u}) :
    SSet.ι₁ ≫ simplicialPathDiagonalCylinder X = 𝟙 _ := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  change (X.map (simplicialPathCut d.unop (SimplexPrefix.endpoint.{u} d.unop 1)).op).app d z = z
  rw [simplicialPathCut_one, op_id, X.map_id]
  rfl

/-- 概要：経路実現は射影と定数切断の合成から恒等射への実際のホモトピーを持つ。
方針：構成した cylinder と両端点の計算を束ねる。
規約：相対部分複体は空。使われ方：零段へのホモトピー同値。 -/
def simplicialPathDiagonalContraction (X : SimplicialObject SSet.{u}) :
    SSet.Homotopy (simplicialPathDiagonalProjection X ≫ simplicialPathDiagonalSection X)
      (𝟙 (simplicialDiagonalFunctor.obj (simplicialPath X))) where
  h := simplicialPathDiagonalCylinder X
  h₀ := simplicialPathDiagonalCylinder_zero X
  h₁ := simplicialPathDiagonalCylinder_one X
  rel := by ext m ⟨⟨z, hz⟩, t⟩; exact hz.elim

end SerrePositivity.KST.SConstruction
