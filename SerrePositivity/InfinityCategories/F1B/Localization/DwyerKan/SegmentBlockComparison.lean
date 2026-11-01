module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordBlock
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.DirectionArrowComparison
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.SegmentParentComparison

/-!
# 連続部分での区間合成と元の区間合成の比較

概要：元の全頂点と列を保つ連続部分の包含は、同方向区間の合成も保つ。
方針：区間の位置の順序同型を使い、両射列の全頂点と隣接射を照合する。
規約：射の類やモデル構造を追加仮定しない。実際の連結への代入は別節で行う。
使われ方：連結の左右の部分区間の合成の回収。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.Segment
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : Word}
  {X Y X' Y' : C}

def blockPosition (B : Word.Block a b) (p q : Fin (a.length + 1)) :
    Fin ((B.vertex q).val - (B.vertex p).val + 1) ≃o Fin (q.val - p.val + 1) :=
  Fin.castOrderIso (congrArg (fun n => n + 1) (B.vertex_sub p q))

lemma block_index (B : Word.Block a b) (p q : Fin (a.length + 1)) (hpq : p ≤ q)
    (k : Fin ((B.vertex q).val - (B.vertex p).val + 1)) :
    index (B.vertex p) (B.vertex q) (B.vertex_monotone hpq) k =
      B.vertex (index p q hpq (blockPosition B p q k)) := by
  apply Fin.ext
  dsimp [index, Word.Block.vertex, blockPosition, Fin.castOrderIso]
  omega

/-- 元の連続部分の射列は、位置の順序同型で元の射列を再添字付けしたもの。 -/
lemma chain_block (B : Word.Block a b) (S : Zigzag W a X Y) (T : Zigzag W b X' Y')
    (hv : ∀ j, T.vertex (B.vertex j) = S.vertex j)
    (ha : ∀ i, HEq (T.arrow (B.column i)) (S.arrow i))
    (d : Direction) (p q : Fin (a.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin a.length, p.val ≤ i.val → i.val < q.val → a.direction i = d) :
    chain d T (B.vertex p) (B.vertex q) (B.vertex_monotone hpq)
        (B.interval_direction d p q hd) =
      (blockPosition B p q).toOrderEmbedding.toOrderHom.toFunctor ⋙ chain d S p q hpq hd := by
  let hObj (k : Fin ((B.vertex q).val - (B.vertex p).val + 1)) :=
    congrArg (Direction.vertex d)
      ((congrArg T.vertex (block_index B p q hpq k)).trans (hv _))
  apply ComposableArrows.ext hObj
  intro k hk
  apply (conj_eqToHom_iff_heq _ _ (hObj ⟨k, by omega⟩) (hObj ⟨k + 1, by omega⟩)).2
  have hn := B.vertex_sub p q
  have hk' : k < q.val - p.val := by omega
  let i : Fin a.length := ⟨p.val + k, by have := q.isLt; omega⟩
  let j : Fin b.length := ⟨(B.vertex p).val + k, by have := (B.vertex q).isLt; omega⟩
  have hij : j = B.column i := Fin.ext (by
    dsimp [j, i, Word.Block.vertex, Word.Block.column]
    omega)
  have hi := hd i (by dsimp [i]; omega) (by dsimp [i]; omega)
  have hj : b.direction j = d :=
    (congrArg b.direction hij).trans ((B.direction_eq i).trans hi)
  change HEq ((chain d T (B.vertex p) (B.vertex q) _ _).map' k (k + 1) (by omega) (by omega))
    ((chain d S p q hpq hd).map' k (k + 1) (by omega) (by omega))
  dsimp only [chain]
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ k hk,
    ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ k hk']
  have hs := (congrArg T.vertex (B.source_eq i)).trans (hv (a.source i))
  have ht := (congrArg T.vertex (B.target_eq i)).trans (hv (a.target i))
  exact (arrow_heq d T hj ((B.direction_eq i).trans hi) hij).trans
    (Direction.arrow_heq_of T S d _ _ _ _ hs ht (ha i))

/-- 連続部分での元の区間合成は、元の小さい語での区間合成と異種等しい。 -/
lemma map_block_heq (B : Word.Block a b) (S : Zigzag W a X Y) (T : Zigzag W b X' Y')
    (hv : ∀ j, T.vertex (B.vertex j) = S.vertex j)
    (ha : ∀ i, HEq (T.arrow (B.column i)) (S.arrow i))
    (d : Direction) (p q : Fin (a.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin a.length, p.val ≤ i.val → i.val < q.val → a.direction i = d) :
    HEq (map d T (B.vertex p) (B.vertex q) (B.vertex_monotone hpq)
        (B.interval_direction d p q hd)) (map d S p q hpq hd) := by
  change HEq (eqToHom _ ≫ (chain d T _ _ _ _).hom ≫ eqToHom _)
    (eqToHom _ ≫ (chain d S p q hpq hd).hom ≫ eqToHom _)
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
    heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  let α : (0 : Fin ((B.vertex q).val - (B.vertex p).val + 1)) ⟶ Fin.last _ :=
    homOfLE (Fin.zero_le _)
  have h := Functor.hcongr_hom (chain_block B S T hv ha d p q hpq hd) α
  refine h.trans (fin_map_heq (chain d S p q hpq hd) ?_ ?_
    ((blockPosition B p q).toOrderEmbedding.toOrderHom.toFunctor.map α)
    (homOfLE (Fin.zero_le _)))
  · apply Fin.ext
    rfl
  · apply Fin.ext
    exact B.vertex_sub p q

end SerrePositivity.EInfinity.Hammock.Segment
