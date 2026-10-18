module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalAdjunction
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# 各行と標準単体から対角模型への評価

概要：二重単体集合の n 行と標準 n 単体の積から、実際の対角単体集合へ写す。
方針：標準単体の元で外側の単体方向を制限し、同じ内側次数で評価する。
規約：Segal 1974 Proposition 1.6 の有限骨格の構造写像。
使われ方：fat realization の付着写像と対角模型の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial ConcreteCategory
open SerrePositivity.BisimplicialModel

/--
概要：n 行と標準 n 単体の積から対角単体集合への標準写像。
方針：標準単体が表す射を外側の関手に適用する。
規約：両方向の作用は自然性で可換になる。
使われ方：骨格の各単体を対角へ送る構造写像。
-/
def diagonalRowEvaluation (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    F.obj (op ⦋n⦌) ⊗ Δ[n] ⟶ diagonal.obj F where
  app d := ↾fun p => (F.map (SSet.stdSimplex.objEquiv p.2).op).app d p.1
  naturality {d e} θ := by
    apply ConcreteCategory.hom_ext
    intro p
    change (F.map (SSet.stdSimplex.objEquiv ((SSet.stdSimplex.obj ⦋n⦌).map θ p.2)).op).app e
      ((F.obj (op ⦋n⦌)).map θ p.1) =
      (F.obj e).map θ ((F.map θ).app d ((F.map (SSet.stdSimplex.objEquiv p.2).op).app d p.1))
    rw [SSet.stdSimplex.map_apply, Equiv.apply_symm_apply, op_comp, F.map_comp]
    change (F.map θ).app e
      ((F.map (SSet.stdSimplex.objEquiv p.2).op).app e ((F.obj (op ⦋n⦌)).map θ p.1)) = _
    calc
      _ = (F.map θ).app e ((F.obj d).map θ
          ((F.map (SSet.stdSimplex.objEquiv p.2).op).app d p.1)) :=
        congrArg (fun y => (F.map θ).app e y)
          (ConcreteCategory.congr_hom
            ((F.map (SSet.stdSimplex.objEquiv p.2).op).naturality θ) p.1)
      _ = _ := ConcreteCategory.congr_hom ((F.map θ).naturality θ)
        ((F.map (SSet.stdSimplex.objEquiv p.2).op).app d p.1)

/--
概要：各行の対角への評価は二重単体集合の射に関して自然である。
方針：外側の自然変換の自然性を同じ内側次数で評価する。
規約：行の番号を固定する。
使われ方：有限骨格の構造写像と比較射の可換性。
-/
@[reassoc] theorem diagonalRowEvaluation_naturality
    {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G) (n : ℕ) :
    (α.app (op ⦋n⦌) ▷ Δ[n]) ≫ diagonalRowEvaluation G n =
      diagonalRowEvaluation F n ≫ diagonal.map α := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro p
  exact (congrArg (fun t => t.app d p.1)
    (α.naturality (SSet.stdSimplex.objEquiv p.2).op)).symm

/--
概要：行の評価は、行の単体作用と標準単体の写像を同じものとして対角へ送る。
方針：関手の合成則で二つの外側の制限を一つにまとめる。
規約：coend の同一視の関係式。射は単射に限らない。
使われ方：骨格の面の貼り付けと対角模型の余極限表示。
-/
@[reassoc] theorem diagonalRowEvaluation_dinaturality
    (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (F.map θ.op ▷ Δ[m]) ≫ diagonalRowEvaluation F m =
      (F.obj (op ⦋n⦌) ◁ SSet.stdSimplex.map θ) ≫ diagonalRowEvaluation F n := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro p
  change (F.map (SSet.stdSimplex.objEquiv p.2).op).app d ((F.map θ.op).app d p.1) =
    (F.map (SSet.stdSimplex.objEquiv ((SSet.stdSimplex.map θ).app d p.2)).op).app d p.1
  have ht : SSet.stdSimplex.objEquiv ((SSet.stdSimplex.map θ).app d p.2) =
      SSet.stdSimplex.objEquiv p.2 ≫ θ := rfl
  rw [ht, op_comp, F.map_comp]
  rfl

/--
概要：各次数の対角の元は、その次数の行の評価の像に入る。
方針：標準単体の恒等の元を選ぶ。
規約：有限の特定の次数の全射性だけを述べる。
使われ方：対角模型の余極限の普遍性の一意性。
-/
theorem diagonalRowEvaluation_identity (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ)
    (x : (diagonal.obj F) _⦋n⦌) :
    (diagonalRowEvaluation F n).app (op ⦋n⦌)
      (x, SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)) = x := by
  change (F.map (𝟙 (op ⦋n⦌))).app (op ⦋n⦌) x = x
  rw [CategoryTheory.Functor.map_id]
  rfl

end SerrePositivity.KST.Comparison
