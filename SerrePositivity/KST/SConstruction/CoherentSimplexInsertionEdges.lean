module
public import SerrePositivity.KST.SConstruction.CoherentInsertionMappingEdges

/-! # 元の coherent 単体の二切断経路と通常射の比較辺
概要：同じ単体から得る二点挿入の実二単体の四辺を、通常射の元の比較辺へ照合する。
方針：端点 Path の通常射の頂点を回収し、豊穣合成の四辺の式に代入する。
規約：全一単体の等号と元の全二単体を保持する。局所 Kan 性は不要。
使われ方：三入力 BF 四面体の全四辺を保存済みの合成面へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}

/-- 元の端点 Path の恒等包含の像は、復号した通常射の頂点の同じ恒等辺。 -/
lemma coherentSimplexEndpointIdentity_edge (s : (SimplicialNerve C) _⦋n⦌)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    ((nerve.edgeMk (𝟙 (coherentEndpointPath
      (show (ULift.up i : ULift.{u} _) ≤ ULift.up j from hij)))).map
        (s.map (.mk (ULift.up i)) (.mk (ULift.up j)))).edge =
      (SSet.Edge.id (SimplicialCategory.homEquiv' _ _ (coherentSimplexArrow s i j hij))).edge := by
  have hv : SimplicialCategory.homEquiv' _ _ (coherentSimplexArrow s i j hij) =
      (s.map (.mk (ULift.up i)) (.mk (ULift.up j))).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ (coherentEndpointPath
          (show (ULift.up i : ULift.{u} _) ≤ ULift.up j from hij))) :=
    Equiv.apply_symm_apply _ _
  rw [nerve.edgeMk_id, SSet.Edge.map_id, hv]
  rfl

/-- 同じ単体の第一切断点を先に挿入した元の実二単体。 -/
def coherentSimplexFirstInsertionTriangle (s : (SimplicialNerve C) _⦋n⦌)
    (i j k l : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :=
  coherentDoubleInsertMappedFirstTriangle (s.map (.mk (ULift.up i)) (.mk (ULift.up l)))
    (show (ULift.up i : ULift.{u} _) ≤ ULift.up j from hij)
    (show (ULift.up j : ULift.{u} _) ≤ ULift.up l from hjk.trans hkl)
    (show (ULift.up i : ULift.{u} _) ≤ ULift.up k from hij.trans hjk)
    (show (ULift.up k : ULift.{u} _) ≤ ULift.up l from hkl)
    (coherentEndpointPath
      (show (ULift.up i : ULift.{u} _) ≤ ULift.up l from (hij.trans hjk).trans hkl))

/-- 同じ単体の第二切断点を先に挿入した元の実二単体。 -/
def coherentSimplexSecondInsertionTriangle (s : (SimplicialNerve C) _⦋n⦌)
    (i j k l : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :=
  coherentDoubleInsertMappedSecondTriangle (s.map (.mk (ULift.up i)) (.mk (ULift.up l)))
    (show (ULift.up i : ULift.{u} _) ≤ ULift.up j from hij)
    (show (ULift.up j : ULift.{u} _) ≤ ULift.up l from hjk.trans hkl)
    (show (ULift.up i : ULift.{u} _) ≤ ULift.up k from hij.trans hjk)
    (show (ULift.up k : ULift.{u} _) ≤ ULift.up l from hkl)
    (coherentEndpointPath
      (show (ULift.up i : ULift.{u} _) ≤ ULift.up l from (hij.trans hjk).trans hkl))

/-- 第一経路の下辺は、元の単体の第一切断による全比較辺。 -/
lemma coherentSimplexFirstInsertion_lower (s : (SimplicialNerve C) _⦋n⦌)
    (i j k l : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    (SimplicialCategory.sHom (s.obj (.mk (ULift.up i))) (s.obj (.mk (ULift.up l)))).δ 2
        (coherentSimplexFirstInsertionTriangle s i j k l hij hjk hkl).simplex =
      (coherentSimplexCompositionEdge s i j l hij (hjk.trans hkl)).edge :=
  coherentDoubleInsertMappedFirstLower _ _ _ _ _

/-- 第二経路の下辺は、元の単体の第二切断による全比較辺。 -/
lemma coherentSimplexSecondInsertion_lower (s : (SimplicialNerve C) _⦋n⦌)
    (i j k l : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    (SimplicialCategory.sHom (s.obj (.mk (ULift.up i))) (s.obj (.mk (ULift.up l)))).δ 2
        (coherentSimplexSecondInsertionTriangle s i j k l hij hjk hkl).simplex =
      (coherentSimplexCompositionEdge s i k l (hij.trans hjk) hkl).edge :=
  coherentDoubleInsertMappedSecondLower _ _ _ _ _

/-- 第一経路の上辺は、復号した第一射の恒等辺と後半の元の比較辺の実豊穣合成。 -/
lemma coherentSimplexFirstInsertion_upper (s : (SimplicialNerve C) _⦋n⦌)
    (i j k l : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    (SimplicialCategory.sHom (s.obj (.mk (ULift.up i))) (s.obj (.mk (ULift.up l)))).δ 0
        (coherentSimplexFirstInsertionTriangle s i j k l hij hjk hkl).simplex =
      (eComp SSet (s.obj (.mk (ULift.up i))) (s.obj (.mk (ULift.up j)))
        (s.obj (.mk (ULift.up l)))).app (Opposite.op ⦋1⦌)
        ((SSet.Edge.id (SimplicialCategory.homEquiv' _ _
            (coherentSimplexArrow s i j hij))).edge,
          (coherentSimplexCompositionEdge s j k l hjk hkl).edge) := by
  have h := coherentDoubleInsertMappedFirstUpper s
    (show (ULift.up i : ULift.{u} _) ≤ ULift.up j from hij)
    (show (ULift.up j : ULift.{u} _) ≤ ULift.up k from hjk)
    (show (ULift.up k : ULift.{u} _) ≤ ULift.up l from hkl)
  rw [coherentSimplexEndpointIdentity_edge] at h
  exact h

/-- 第二経路の上辺は、前半の元の比較辺と復号した最終射の恒等辺の実豊穣合成。 -/
lemma coherentSimplexSecondInsertion_upper (s : (SimplicialNerve C) _⦋n⦌)
    (i j k l : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    (SimplicialCategory.sHom (s.obj (.mk (ULift.up i))) (s.obj (.mk (ULift.up l)))).δ 0
        (coherentSimplexSecondInsertionTriangle s i j k l hij hjk hkl).simplex =
      (eComp SSet (s.obj (.mk (ULift.up i))) (s.obj (.mk (ULift.up k)))
        (s.obj (.mk (ULift.up l)))).app (Opposite.op ⦋1⦌)
        ((coherentSimplexCompositionEdge s i j k hij hjk).edge,
          (SSet.Edge.id (SimplicialCategory.homEquiv' _ _
            (coherentSimplexArrow s k l hkl))).edge) := by
  have h := coherentDoubleInsertMappedSecondUpper s
    (show (ULift.up i : ULift.{u} _) ≤ ULift.up j from hij)
    (show (ULift.up j : ULift.{u} _) ≤ ULift.up k from hjk)
    (show (ULift.up k : ULift.{u} _) ≤ ULift.up l from hkl)
  rw [coherentSimplexEndpointIdentity_edge] at h
  exact h

end SerrePositivity.KST.SConstruction
