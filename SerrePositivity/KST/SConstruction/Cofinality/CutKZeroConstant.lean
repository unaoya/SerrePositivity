module
public import SerrePositivity.KST.SConstruction.Cofinality.CutKZeroRestriction

/-!
概要：定値の端点制限は元の S 構成内で零対象となる。
方針：全 Ar 成分が同じ対角に写ることを検査する。
規約：元の gapped 図式の対角零性を使う。
使われ方：障害余核の左右の区間延長の交差項の消滅。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：定値の端点制限の元の像は S_m 内で零対象。
方針：各 Ar 成分の評価が元の対角評価であることを使う。
規約：元の頂点を別の零対象へ取り替えない。
使われ方：K₀ における定値制限の消滅。 -/
lemma cofinalitySRestriction_constant_isZero {m n : ℕ} (X : StableModel.{u})
    (i : Fin (n + 1)) (v : (sStableModel n X).carrier _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((cofinalitySRestriction X
      (OrderHom.const (Fin (m + 1)) i)).val.app (Opposite.op ⦋0⦌) v) := by
  apply gappedVertex_isZero_of_pointwise
  intro a
  obtain ⟨b, rfl⟩ := nerveEquiv.symm.surjective a
  have he := sMap_evaluate_vertex (OrderHom.const (Fin (m + 1)) i) v
    (ComposableArrows.mk₀ b)
  have ha : (arNerveMap (OrderHom.const (Fin (m + 1)) i)).app
      (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ b) =
      ComposableArrows.mk₀ (arObj i i le_rfl) := by
    apply ComposableArrows.ext₀
    apply ULift.ext
    apply Subtype.ext
    rfl
  rw [ha] at he
  exact (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex he).mpr (sConstructionVertex_diagonal_isZero v i)

/-- 概要：定値端点制限の三角圏 K₀ 作用は零。
方針：対象生成元の像が実際に零対象であることを使う。
規約：元の完全射の誘導準同型。
使われ方：区間延長と反対側の制限の交差項を除く。 -/
lemma cutKZeroRestriction_constant {m n : ℕ} (X : StableModel.{u})
    (i : Fin (n + 1)) :
    cutKZeroRestriction X (OrderHom.const (Fin (m + 1)) i) = 0 := by
  apply TriangulatedK0.hom_ext (C := hoFunctor.obj (sStableModel n X).carrier)
  intro a
  obtain ⟨v, rfl⟩ := Truncated.HomotopyCategory.mk_surjective a
  change triangulatedKZeroSourceMap (cofinalitySRestriction X
      (OrderHom.const (Fin (m + 1)) i)) (TriangulatedK0.mk (HomotopyCategory.mk v)) = 0
  rw [triangulatedKZeroSourceMap_mk]
  exact TriangulatedK0.mk_of_isZero _
    (cofinalitySRestriction_constant_isZero (m := m) X i v).isZeroHo

end SerrePositivity.KST.SConstruction.Cofinality
