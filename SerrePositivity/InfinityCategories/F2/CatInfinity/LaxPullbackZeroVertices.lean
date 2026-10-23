module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackTerminalVertices
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackInitialVertices
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackVertexEquiv
public import SerrePositivity.InfinityCategories.Stable.ExactFunctor

/-!
概要：零対象を保つ二関手の lax pullback は零対象を持つ。
方針：両入力と像の始対象性・終対象性を別々に証明する。
規約：実際の零頂点を構成し、安定性を仮定するフィールドは追加しない。
使われ方：Tamme Lemma 8(iv) の安定性への零対象の入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]

/-- 概要：両入力とその像が零対象である頂点は lax pullback の零対象。
方針：成分ごとの始対象と終対象の二つの判定を合わせる。
規約：元の指定矢印をそのまま使う。
使われ方：有限極限余極限からの安定性の構成。 -/
lemma isZeroVertex_laxPullback_of_components (p : A ⟶ C) (q : B ⟶ C)
    (x : (laxPullback p q) _⦋0⦌)
    (ha : IsZeroVertex ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) x))
    (hb : IsZeroVertex ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x))
    (hp : IsZeroVertex (p.app (Opposite.op ⦋0⦌)
      ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) x)))
    (hq : IsZeroVertex (q.app (Opposite.op ⦋0⦌)
      ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x))) : IsZeroVertex x :=
  ⟨isInitialVertex_laxPullback_of_components p q x ha.1 hb.1 hp.1 hq.1,
    isTerminalVertex_laxPullback_of_components p q x ha.2 hb.2 hp.2 hq.2⟩

/-- 概要：零対象を保つ二関手の lax pullback は零対象を持つ。
方針：二つの零対象の像を結ぶ辺を選び、三つ組の全単射で頂点へ戻す。
規約：C の零対象の選択や二関手の安定性は仮定しない。
使われ方：Tamme Lemma 8(iv) の pointed 条件。 -/
lemma exists_zeroVertex_laxPullback_with_components (p : A ⟶ C) (q : B ⟶ C)
    [HasZeroVertex A] [HasZeroVertex B]
    (hp : PreservesZeroVertices p) (hq : PreservesZeroVertices q) :
    ∃ x : (laxPullback p q) _⦋0⦌, IsZeroVertex x ∧
      IsZeroVertex ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) x) ∧
      IsZeroVertex ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x) := by
  let a := chosenZeroVertex A
  let b := chosenZeroVertex B
  obtain ⟨e⟩ := (hq b.vertex b.isZero).2.nonempty_edge (p.app _ a.vertex)
  let d : LaxPullbackVertexData p q :=
    ⟨a.vertex, b.vertex, e.edge, e.src_eq, e.tgt_eq⟩
  let x := laxPullbackVertexOfData p q d
  have h := laxPullbackVertexData_ofData p q d
  have ha : (laxPullbackFst p q).app (Opposite.op ⦋0⦌) x = a.vertex :=
    congrArg LaxPullbackVertexData.left h
  have hb : (laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x = b.vertex :=
    congrArg LaxPullbackVertexData.right h
  have hza : IsZeroVertex ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) x) :=
    ha.symm ▸ a.isZero
  have hzb : IsZeroVertex ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x) :=
    hb.symm ▸ b.isZero
  exact ⟨x, isZeroVertex_laxPullback_of_components p q x hza hzb (hp _ hza) (hq _ hzb),
    hza, hzb⟩

/-- 概要：零対象を保つ二関手の lax pullback は零対象を持つ。
方針：二射影も零となる頂点の存在を使う。
規約：零対象の存在と選択を区別する。
使われ方：Tamme Lemma 8(iv) の pointed 条件。 -/
lemma hasZeroVertex_laxPullback_of_preservesZero (p : A ⟶ C) (q : B ⟶ C)
    [HasZeroVertex A] [HasZeroVertex B]
    (hp : PreservesZeroVertices p) (hq : PreservesZeroVertices q) :
    HasZeroVertex (laxPullback p q) := by
  obtain ⟨x, hx, _, _⟩ := exists_zeroVertex_laxPullback_with_components p q hp hq
  exact ⟨x, hx⟩

end SerrePositivity.InfinityCategories.F2
