module
public import SerrePositivity.InfinityCategories.Derived.SemifreeSubcategory
public import SerrePositivity.InfinityCategories.DGNerve

/-! # Semifree 複体の dg nerve

概要：導来単体的集合とその零・一・二単体を定義する。
方針：N1 の公開同値を semifree dg 部分圏へ具体化する。
規約：quasicategory 性は N2 の完了後に扱う。
使われ方：導来 ∞ 圏のホモトピー圏と安定性の比較の入口。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
open scoped Simplicial
variable (S : Type u) [CommRing S]

/-- 概要：semifree 複体の dg nerve としての導来単体的集合。
方針：一般の dg nerve を充満 dg 部分圏に適用する。
規約：対象宇宙は u+1。使われ方：導来 ∞ 圏の基礎データ。 -/
def derivedInfinityCategory : SSet.{u + 1} := dgNerve S (Semifree S)

/-- 概要：導来単体的集合の n 単体は semifree 複体間の dg nerve 単体。
方針：定義を評価する。規約：cochain 規約。使われ方：単体の成分の計算。 -/
theorem derivedInfinityCategory_obj (n : ℕ) :
    (derivedInfinityCategory S) _⦋n⦌ = DGNerve.Simplex S (Semifree S) n := rfl

/-- 概要：零単体は semifree 複体と同値である。
方針：N1 の頂点同値を適用する。規約：filtration の存在は命題。
使われ方：導来単体的集合の対象の解釈。 -/
def derivedInfinityCategoryVertexEquiv :
    (derivedInfinityCategory S) _⦋0⦌ ≃ Semifree S := dgNerve.vertexEquiv S (Semifree S)

/-- 概要：一単体は二つの semifree 複体とその間の閉零射である。
方針：N1 の辺同値を適用する。規約：射は Hom 複体の零 cycle。
使われ方：導来単体的集合の射の解釈。 -/
def derivedInfinityCategoryEdgeEquiv :
    (derivedInfinityCategory S) _⦋1⦌ ≃
      Σ obj : Fin 2 → Semifree S,
        zeroCycles (homObject S (Semifree S) (obj 0) (obj 1)) :=
  dgNerve.edgeEquiv S (Semifree S)

/-- 概要：二単体は三つの閉零射と合成を埋める次数 −1 のホモトピーである。
方針：N1 の三角形同値を適用する。規約：微分は合成と第三辺の差。
使われ方：導来単体的集合の合成とホモトピーの解釈。 -/
def derivedInfinityCategoryTriangleEquiv :
    (derivedInfinityCategory S) _⦋2⦌ ≃ DGNerve.TriangleData S (Semifree S) :=
  dgNerve.triangleEquiv S (Semifree S)

end SerrePositivity.InfinityCategories
