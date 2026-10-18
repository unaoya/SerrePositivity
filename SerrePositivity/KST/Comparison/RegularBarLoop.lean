module

public import SerrePositivity.KST.Comparison.RegularBarContraction
public import SerrePositivity.KST.Comparison.BarEdge

/-!
# 正則 bar の収縮と標準ループ族

概要：正則 bar の収縮をファイバーへ制限し射影すると標準ループ族になることを示す。
方針：単位から各元への正則作用の射のラベルを一対象圏で読む。
規約：Segal 1974 Proposition 1.5 のファイバーからループ空間への標準写像。
使われ方：ホモトピーファイバー比較が与える写像と標準写像の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

/--
概要：一つの元への収縮路の射影はその元をラベルとする辺である。
方針：区間圏の三つの射でラベルを直接計算する。
規約：Segal 1974 Proposition 1.5。正則左作用と SingleObj の合成順序を保持する。
使われ方：対角の標準ループ族の同定。
-/
theorem regularActionInterval_projection (T : MonCat.{u}) (a : T) :
    (𝟭 (Fin 2)).prod' ((Functor.const (Fin 2)).obj (RegularAction.mk a)) ⋙
      regularActionInterval T ⋙ regularActionProjection T = monoidEdgeSimplex T a := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  fin_cases i <;> fin_cases j
  all_goals first
  | exact False.elim (by have hle : (1 : Fin 2) ≤ 0 := leOfHom f; simp at hle)
  | simp [regularActionInterval, NerveHomotopy.interval, Functor.uncurry,
      regularActionContraction, regularActionProjection, ComposableArrows.mk₁,
      monoidEdgeSimplex, SingleObj.id_as_one, SingleObj.comp_as_mul]

/--
概要：正則 bar の収縮をファイバーへ制限して射影すると標準辺写像を得る。
方針：各次数で区間関手の射影の等式を区間単体に沿って引き戻す。
規約：Segal 1974 Proposition 1.5 の M→ΩBM の随伴写像との一致。
使われ方：群完備化比較が計算する写像を固定する。
-/
theorem regularBarContraction_projection (M : SimplicialObject MonCat.{u}) :
    regularBarFiberMap M ▷ (Δ[1] : SSet.{u}) ≫ regularBarContractionMap M ≫
      regularBarProjection M = monoidBarEdgeMap M := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  change M.obj n × (Δ[1] : SSet.{u}).obj n at p
  let β := (SSet.stdSimplex.objEquiv p.2).toOrderHom.monotone.functor
  change β ⋙ (𝟭 (Fin 2)).prod' ((Functor.const (Fin 2)).obj (RegularAction.mk p.1)) ⋙
    regularActionInterval (M.obj n) ⋙ regularActionProjection (M.obj n) =
      β ⋙ monoidEdgeSimplex (M.obj n) p.1
  exact congrArg (fun F => β ⋙ F) (regularActionInterval_projection (M.obj n) p.1)

end SerrePositivity.KST.Comparison
