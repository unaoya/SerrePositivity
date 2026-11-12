module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveConstantEvaluation

/-!
概要：重み付き図式の最後の成分と、単体の制限に対する輸送の計算。
方針：重みの自然性と初区間の分解を使い、最後の頂点を保つ場合には輸送が同型と示す。
規約：有限順序集合上の係数関手は任意。
使われ方：Kerodon §5.3.3（Tag 025W）、係数充填から再構成したホーン面の最後の成分の一致。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：制限した図式の最後の成分を輸送すると、元の最後の成分の制限となる。
方針：α の最後の頂点の像から終点への自然性と、初区間の分解を使う。
規約：α は最後の頂点を保たなくてもよい。
使われ方：Kerodon §5.3.3（Tag 025W）、元の weighted nerve の各面と係数充填の比較。 -/
lemma weightedNerveDiagram_terminal_transport {m n : ℕ}
    (G : Fin (n + 1) ⥤ SSet.{u}) (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ G)
    (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeightRestriction α ≫
        CategoryTheory.Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor τ).app
        (Fin.last m) ≫ G.map (homOfLE (Fin.le_last (α.toOrderHom (Fin.last m)))) =
      stdSimplex.map α ≫ τ.app (Fin.last n) := by
  let i := α.toOrderHom (Fin.last m)
  have ht := τ.naturality (homOfLE (Fin.le_last i))
  change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n _) ≫ τ.app (Fin.last n) =
    τ.app i ≫ G.map (homOfLE (Fin.le_last i)) at ht
  change (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α (Fin.last m)) ≫ τ.app i) ≫
      G.map (homOfLE (Fin.le_last i)) = _
  rw [Category.assoc, ← ht, ← Category.assoc, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun q ↦ stdSimplex.map q ≫ τ.app (Fin.last n))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction_last_factor α)

/-- 概要：最後の頂点を保つ単調写像の末端から終点への係数輸送は同型。
方針：有限順序集合での輸送射を頂点の等式の同型と同定し、関手で写す。
規約：係数関手 G の各射の一般の可逆性は不要。
使われ方：Kerodon §5.3.3（Tag 025W）、最後以外の面の係数輸送を消去する判定。 -/
lemma weightedNerveDiagram_terminal_transport_isIso {m n : ℕ}
    (G : Fin (n + 1) ⥤ SSet.{u}) (α : ⦋m⦌ ⟶ ⦋n⦌)
    (h : α.toOrderHom (Fin.last m) = Fin.last n) :
    IsIso (G.map (homOfLE (Fin.le_last (α.toOrderHom (Fin.last m))))) := by
  let f : α.toOrderHom (Fin.last m) ⟶ Fin.last n := homOfLE (Fin.le_last _)
  have hf : f = eqToHom h := Subsingleton.elim _ _
  have : IsIso f := by rw [hf]; infer_instance
  exact inferInstanceAs (IsIso (G.map f))

/-- 概要：等しい weighted nerve の単体の最後の成分は異種等号で等しい。
方針：単体の等式を消去し、依存する係数値を同時に同定する。
規約：底の射列の表示が異なる場合も扱う。
使われ方：Kerodon §5.3.3（Tag 025W）、ホーン面の交わりの等式から係数成分を回収する。 -/
lemma weightedNerveSimplex_last_heq {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n} (h : s = t) :
    HEq (s.2.app (Fin.last n)) (t.2.app (Fin.last n)) := by
  cases h
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
