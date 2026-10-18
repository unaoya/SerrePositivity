module

public import SerrePositivity.KST.Comparison.MonoidComponents
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# モノイドの元を bar のループの辺にする写像

概要：モノイドの各元が一対象圏の辺を与える構成を全単体次数で自然にする。
方針：bar の内側の一次単体を区間の単体に沿って引き戻す。
規約：Segal 1974 Proposition 1.5 の M→ΩBM の随伴写像の構成部分。
使われ方：群完備化写像と分類空間のホモトピー群の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.Comparison

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

/--
概要：モノイドの元を一対象圏の nerve の辺にする。
方針：その元を唯一の対象の自己射と読む。
規約：KST Lemma 2.13、Segal 1974 Proposition 1.5。
使われ方：bar のループへの標準写像。
-/
def monoidEdgeSimplex (T : MonCat.{u}) (m : T) : (nerve (SingleObj T)) _⦋1⦌ :=
  ComposableArrows.mk₁ (show SingleObj.star T ⟶ SingleObj.star T from m)

/--
概要：辺を作る操作はモノイド準同型と可換である。
方針：長さ一の図式の二対象と一つの射で比較する。
規約：KST Lemma 2.13 の自然性。逆元は使わない。
使われ方：bar のループ写像の単体作用との可換性。
-/
theorem monoidEdgeSimplex_map {T U : MonCat.{u}} (f : T ⟶ U) (m : T) :
    ((SingleObj.mapHom T U f.hom).mapComposableArrows 1).obj (monoidEdgeSimplex T m) =
      monoidEdgeSimplex U (f.hom m) := by
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · rfl
  · rfl
  · simp [monoidEdgeSimplex]

/--
概要：n 次のモノイドの元と区間の n 単体から bar の n 単体を作る。
方針：元が与える内側の辺を、区間の単調写像に沿って引き戻す。
規約：群状性は不要。Segal 1974 Proposition 1.5 の随伴写像。
使われ方：全次数の bar のループの族。
-/
def monoidBarEdgeAt (M : SimplicialObject MonCat.{u}) (n : ℕ)
    (m : M.obj (op ⦋n⦌)) (t : (Δ[1] : SSet.{u}) _⦋n⦌) : (monoidBar M) _⦋n⦌ :=
  (monoidEdgeSimplex (M.obj (op ⦋n⦌)) m).whiskerLeft
    (SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv t)).toFunctor

/--
概要：モノイドの元を bar の区間内の辺へ送る単体的写像。
方針：各次数で辺を引き戻し、準同型による辺の自然性を使う。
規約：KST Lemma 2.13、Segal 1974 Proposition 1.5 の M→ΩBM の随伴側。
使われ方：Kan 置換後の実際の群完備化写像。
-/
def monoidBarEdgeMap (M : SimplicialObject MonCat.{u}) :
    monoidSpace M ⊗ (Δ[1] : SSet.{u}) ⟶ monoidBar M where
  app n := TypeCat.ofHom (fun p => monoidBarEdgeAt M n.unop.len p.1 p.2)
  naturality i j f := by
    apply ConcreteCategory.hom_ext
    intro p
    let α := (SimplexCategory.toCat.map f.unop).toFunctor
    let β := (SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv p.2)).toFunctor
    let F := SingleObj.mapHom (M.obj i) (M.obj j) (M.map f).hom
    symm
    change α ⋙ β ⋙ monoidEdgeSimplex (M.obj i) p.1 ⋙ F =
      α ⋙ β ⋙ monoidEdgeSimplex (M.obj j) ((M.map f).hom p.1)
    exact congrArg (fun K => α ⋙ β ⋙ K) (monoidEdgeSimplex_map (M.map f) p.1)

/--
概要：区間の端点に定数の単体では bar の辺写像も基点に定数となる。
方針：一対象圏の辺を定数の単調写像へ制限すると全ての射が単位になる。
規約：Segal 1974 Proposition 1.5 の基点付きループ写像の端点条件。
使われ方：M で添字付けられた基点ループの族。
-/
theorem monoidBarEdgeAt_const (M : SimplicialObject MonCat.{u}) (n : ℕ)
    (m : M.obj (op ⦋n⦌)) (a : Fin 2) :
    monoidBarEdgeAt M n m (SSet.stdSimplex.const 1 a (op ⦋n⦌)) =
      (monoidBar M).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op (monoidBarBasepoint M) := by
  fin_cases a <;> refine ComposableArrows.ext (fun _ => rfl) ?_
  all_goals
    intro i hi
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change (1 : M.obj (op ⦋n⦌)) =
      (M.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op).hom 1
    exact (map_one _).symm

/--
概要：bar の辺写像の始点は分類空間の基点である。
方針：区間の零端点を全次数で評価する。
規約：Segal 1974 Proposition 1.5 のループ族の始点条件。
使われ方：群完備化写像の随伴。
-/
theorem monoidBarEdgeMap_zero (M : SimplicialObject MonCat.{u}) :
    SSet.ι₀ ≫ monoidBarEdgeMap M = SSet.const (monoidBarBasepoint M) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro m
  exact monoidBarEdgeAt_const M n.unop.len m 0

/--
概要：bar の辺写像の終点も分類空間の基点である。
方針：区間の一端点を全次数で評価する。
規約：Segal 1974 Proposition 1.5 のループ族の終点条件。
使われ方：群完備化写像の随伴。
-/
theorem monoidBarEdgeMap_one (M : SimplicialObject MonCat.{u}) :
    SSet.ι₁ ≫ monoidBarEdgeMap M = SSet.const (monoidBarBasepoint M) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro m
  exact monoidBarEdgeAt_const M n.unop.len m 1

/--
概要：各元が与える基点ループの族を実単体的ホモトピーとして束ねる。
方針：区間への随伴側を使い、両端が基点に一致することを証明する。
規約：Segal 1974 Proposition 1.5 の標準写像の構成。比較同値性はここでは主張しない。
使われ方：Kan 置換と基点付き内部 Hom による M→ΩBM の構成。
-/
def monoidBarLoopFamily (M : SimplicialObject MonCat.{u}) :
    SSet.Homotopy (SSet.const (X := monoidSpace M) (monoidBarBasepoint M))
      (SSet.const (monoidBarBasepoint M)) where
  h := monoidBarEdgeMap M
  h₀ := monoidBarEdgeMap_zero M
  h₁ := monoidBarEdgeMap_one M
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property


end SerrePositivity.KST.Comparison
