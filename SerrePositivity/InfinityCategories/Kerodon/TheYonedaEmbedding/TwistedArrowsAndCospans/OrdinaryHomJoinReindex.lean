module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomJoinChains

/-!
概要：Hom の元の圏の同じ join 射列は全ての順序写像による再添字と可換。
方針：新しい最初の射を、元の射列の可換四角形で元の最初の射へ戻す。
規約：順序写像は単射でなくてもよく、面と退化を同時に扱う。
使われ方：Kerodon Proposition 8.1.1.10（Tag 03JN）、HTT 5.1.5.6 の指定 Yoneda の全族比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
variable {C : Type u} [SmallCategory C] {m n : ℕ}

/-- 源の反対の射列は、順序写像の反対による前合成で厳密に再添字される。
Kerodon Proposition 8.1.1.10（Tag 03JN）、源の全射列の法則。 -/
lemma ordinaryHomSourceChain_reindex (s : ComposableArrows (OrdinaryHomElements C) n)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    ordinaryHomSourceChain (α.toFunctor ⋙ s) = α.toFunctor.op ⋙ ordinaryHomSourceChain s := rfl

/-- 標的の射列も、元の順序写像による同じ前合成で再添字される。
Kerodon Proposition 8.1.1.10（Tag 03JN）、標的の全射列の法則。 -/
lemma ordinaryHomTargetChain_reindex (s : ComposableArrows (OrdinaryHomElements C) n)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    ordinaryHomTargetChain (α.toFunctor ⋙ s) = α.toFunctor ⋙ ordinaryHomTargetChain s := rfl

/-- 全交差射の族は、最初の頂点を保たない順序写像でも同じ再添字と可換。
Kerodon Proposition 8.1.1.10（Tag 03JN）、中心の射の選び直しに依存しない法則。 -/
lemma ordinaryHomCrossChain_reindex (s : ComposableArrows (OrdinaryHomElements C) n)
    (α : Fin (m + 1) →o Fin (n + 1)) (i j : Fin (m + 1)) :
    (ordinaryHomCrossChain (α.toFunctor ⋙ s)).app (Opposite.op i, j) =
      (ordinaryHomCrossChain s).app (Opposite.op (α i), α j) := by
  have hs : (s.map (homOfLE (Fin.zero_le (α i)))).hom.1.unop =
      (s.map (homOfLE (α.monotone (Fin.zero_le i)))).hom.1.unop ≫
        (s.map (homOfLE (Fin.zero_le (α 0)))).hom.1.unop := by
    have h : homOfLE (Fin.zero_le (α i)) =
        homOfLE (Fin.zero_le (α 0)) ≫ homOfLE (α.monotone (Fin.zero_le i)) :=
      Subsingleton.elim _ _
    rw [h, s.map_comp]
    rfl
  have ht : (s.map (homOfLE (Fin.zero_le (α j)))).hom.2 =
      (s.map (homOfLE (Fin.zero_le (α 0)))).hom.2 ≫
        (s.map (homOfLE (α.monotone (Fin.zero_le j)))).hom.2 := by
    have h : homOfLE (Fin.zero_le (α j)) =
        homOfLE (Fin.zero_le (α 0)) ≫ homOfLE (α.monotone (Fin.zero_le j)) :=
      Subsingleton.elim _ _
    rw [h, s.map_comp]
    rfl
  change (s.map (homOfLE (α.monotone (Fin.zero_le i)))).hom.1.unop ≫
      (s.obj (α 0)).val ≫ (s.map (homOfLE (α.monotone (Fin.zero_le j)))).hom.2 = _
  rw [← ordinaryHomElements_map_val (s.map (homOfLE (Fin.zero_le (α 0))))]
  change _ = (s.map (homOfLE (Fin.zero_le (α i)))).hom.1.unop ≫
    (s.obj 0).val ≫ (s.map (homOfLE (Fin.zero_le (α j)))).hom.2
  rw [hs, ht]
  simp only [Category.assoc]

/-- 同じ join の全関手は、左右両方の順序写像による再添字と厳密に可換。
Kerodon Proposition 8.1.1.10（Tag 03JN）。全対象・全射を含む等式。 -/
lemma ordinaryHomJoinChain_reindex (s : ComposableArrows (OrdinaryHomElements C) n)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    CategoryTheory.Join.mapPair α.toFunctor.op α.toFunctor ⋙ ordinaryHomJoinChain s =
      ordinaryHomJoinChain (α.toFunctor ⋙ s) := by
  refine CategoryTheory.Functor.hext (fun x => by cases x <;> rfl) ?_
  intro x y f
  cases f using CategoryTheory.Join.homInduction with
  | left a b f => rfl
  | right a b f => rfl
  | edge a b =>
    change HEq ((ordinaryHomCrossChain s).app (Opposite.op (α a.unop), α b))
      ((ordinaryHomCrossChain (α.toFunctor ⋙ s)).app (a, b))
    exact heq_of_eq (ordinaryHomCrossChain_reindex s α a.unop b).symm

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
