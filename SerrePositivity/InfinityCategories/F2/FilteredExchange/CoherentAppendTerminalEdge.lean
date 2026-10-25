module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentAppendVertexEdge

/-!
概要：指定射を追加した全単体の最終辺は、その同じ元の指定射で固定される。
方針：最終頂点への制限の自然性と零次元の追加の計算を使う。
規約：全単体の他の部分には依存しない。使われ方：同じ固定辺上の実 slice 族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 任意の次数の標準単体の元の最終頂点を選ぶ添字写像。 -/
def simplexTerminalVertex (n : ℕ) : ⦋0⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom (OrderHom.const _ (Fin.last n))

/-- 元の全単体の表示変更は、指定した同じ射の追加を厳密に保持する。 -/
lemma coherentSimplexAppendMorphism_of_source_eq {n : ℕ}
    {s t : (SimplicialNerve C) _⦋n⦌} (e : s = t) {Z W : C}
    (hs : s.obj ⟨ULift.up (Fin.last n)⟩ = Z)
    (ht : t.obj ⟨ULift.up (Fin.last n)⟩ = Z) (g : Z ⟶ W) :
    coherentSimplexAppendMorphism s (eqToHom hs ≫ g) =
      coherentSimplexAppendMorphism t (eqToHom ht ≫ g) := by
  cases e
  rfl

/-- 追加した実全単体の最後の辺は、元の同じ指定射の coherent 辺。 -/
lemma coherentSimplexAppendMorphism_terminalEdge {n : ℕ}
    (s : (SimplicialNerve C) _⦋n⦌) {Y : C}
    (g : s.obj ⟨ULift.up (Fin.last n)⟩ ⟶ Y) :
    (SimplicialNerve C).map (PinchedHom.extend (simplexTerminalVertex n)).op
        (coherentSimplexAppendMorphism s g) = (coherentNerveEdge g).edge := by
  have hα : (simplexTerminalVertex n).toOrderHom (Fin.last 0) = Fin.last n := rfl
  have h₀ : (SimplicialNerve C).map (simplexTerminalVertex n).op s =
      coherentNerveVertex (s.obj ⟨ULift.up (Fin.last n)⟩) := by
    apply (coherentNerveVertexEquiv C).symm.injective
    exact coherentSimplexLastPreserving_last (simplexTerminalVertex n) hα s
  calc
    _ = coherentSimplexAppendMorphism
        ((SimplicialNerve C).map (simplexTerminalVertex n).op s)
        (eqToHom (coherentSimplexLastPreserving_last (simplexTerminalVertex n) hα s) ≫ g) :=
      coherentSimplexAppendMorphism_lastPreserving (simplexTerminalVertex n) hα s g
    _ = coherentSimplexAppendMorphism (coherentNerveVertex _) g := by
      have h := coherentSimplexAppendMorphism_of_source_eq h₀
        (coherentSimplexLastPreserving_last (simplexTerminalVertex n) hα s) rfl g
      simpa only [eqToHom_refl, Category.id_comp] using h
    _ = _ := coherentSimplexAppendMorphism_vertex g

/-- 元の最終対象の表示を戻しても、追加した実単体の同じ最終辺を保持する。 -/
lemma coherentSimplexAppendMorphism_terminalEdge_of_eq {n : ℕ}
    (s : (SimplicialNerve C) _⦋n⦌) {Z W : C}
    (hs : s.obj ⟨ULift.up (Fin.last n)⟩ = Z) (g : Z ⟶ W) :
    (SimplicialNerve C).map (PinchedHom.extend (simplexTerminalVertex n)).op
        (coherentSimplexAppendMorphism s (eqToHom hs ≫ g)) = (coherentNerveEdge g).edge := by
  cases hs
  simpa only [eqToHom_refl, Category.id_comp] using
    coherentSimplexAppendMorphism_terminalEdge s g

end SerrePositivity.InfinityCategories.F2
