module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseEquivalencePaths
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniversePullbacks
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseVertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.ConeIteratedSliceIso

/-!
概要：Kan な標的への任意の比較射の導来 fiber と ULift の厳密な同型。
方針：path 置換の引き戻しの宇宙を移し、終点評価の可換式でその頂点 fiber を移す。
規約：元の射の fibration 性も始域の Kan 性も要求しない。
使われ方：HTT 4.2.4.1、反転比較の ULift を導来 fiber の外へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：path 置換の ULift の全空間は持ち上げた元の射の path 置換の引き戻しを与える。
方針：元の引き戻しを ULift で保存し、path の標準同型で右上の対象を移す。
規約：標的 B の Kan 性を使って可逆 path の同型を得る。
使われ方：path 置換の全空間の宇宙の標準同型。 -/
lemma uliftPathReplacement_isPullback {E B : SSet.{u}} [KanComplex B] (p : E ⟶ B) :
    IsPullback
      ((SSet.uliftFunctor.{v, u}).map (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) p) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftEquivalencePathIso.{u, v} B).hom)
      ((SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((SSet.uliftFunctor.{v, u}).obj B) 0)
      ((SSet.uliftFunctor.{v, u}).map p) := by
  let h := (IsPullback.of_hasPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) p).map
    (SSet.uliftFunctor.{v, u})
  exact h.of_iso (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftEquivalencePathIso B) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection])
    (by simpa only [Iso.refl_hom, Category.comp_id] using
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftEquivalencePathIso_hom_endpoint.{u, v} B 0).symm) (by simp)

/-- 概要：元の射の path 置換の ULift は持ち上げた射の path 置換と厳密に同型。
方針：同じ二射の引き戻しの普遍性で同型を作る。
規約：元の始域への射影と可逆 path 成分を保持する。
使われ方：導来 fiber を取る前の全空間の宇宙の移送。 -/
def uliftPathReplacementIso {E B : SSet.{u}} [KanComplex B] (p : E ⟶ B) :
    (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement p) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement ((SSet.uliftFunctor.{v, u}).map p) :=
  (uliftPathReplacement_isPullback.{u, v} p).isoPullback

/-- 概要：path 置換の ULift の同型は可逆 path 成分の標準比較と可換。
方針：引き戻し比較同型の第一射影を計算する。
規約：可逆 path の向きは保持する。
使われ方：終点評価との厳密な可換式。 -/
lemma uliftPathReplacementIso_hom_path {E B : SSet.{u}} [KanComplex B] (p : E ⟶ B) :
    (uliftPathReplacementIso.{u, v} p).hom ≫ pullback.fst
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((SSet.uliftFunctor.{v, u}).obj B) 0)
        ((SSet.uliftFunctor.{v, u}).map p) =
      (SSet.uliftFunctor.{v, u}).map (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) p) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftEquivalencePathIso.{u, v} B).hom :=
  (uliftPathReplacement_isPullback.{u, v} p).isoPullback_hom_fst

/-- 概要：path 置換の ULift の同型は元の始域への射影を保持する。
方針：引き戻し比較同型の第二射影を計算する。
規約：元の始域は持ち上げた E そのもの。
使われ方：導来 fiber の源成分の保持。 -/
lemma uliftPathReplacementIso_hom_source {E B : SSet.{u}} [KanComplex B] (p : E ⟶ B) :
    (uliftPathReplacementIso.{u, v} p).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection ((SSet.uliftFunctor.{v, u}).map p) =
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection p) :=
  (uliftPathReplacement_isPullback.{u, v} p).isoPullback_hom_snd

/-- 概要：path 置換の ULift の同型は指定した終点への比較射と厳密に可換。
方針：path 成分の可換式と可逆 path の終点評価の比較を合成する。
規約：底は持ち上げた B であり、点も ULift.up で移す。
使われ方：導来 fiber の固定条件を同じ底上で移す。 -/
lemma uliftPathReplacementIso_hom_target {E B : SSet.{u}} [KanComplex B] (p : E ⟶ B) :
    (uliftPathReplacementIso.{u, v} p).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap ((SSet.uliftFunctor.{v, u}).map p) =
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) := by
  change _ ≫ (pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1) = _
  rw [← Category.assoc, uliftPathReplacementIso_hom_path, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftEquivalencePathIso_hom_endpoint, ← CategoryTheory.Functor.map_comp]
  rfl

/-- 概要：元の比較射の導来 fiber の ULift は、持ち上げた比較射の同じ持ち上げた点の fiber と同型。
方針：頂点 fiber と ULift の交換同型に、path 置換の底上の厳密な同型を合成する。
規約：元の射の fibration 性や始域の Kan 性は不要。標的の Kan 性だけを要求する。
使われ方：HTT 4.2.4.1、ULift 後の反転比較の fiber から元の宇宙の fiber を復元する。 -/
def uliftComparisonFiberIso {E B : SSet.{u}} [KanComplex B] (p : E ⟶ B) (b : B _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber p b) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftVertexFiberIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) b ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.vertexFiberIsoOfOverIso _ _ (uliftPathReplacementIso.{u, v} p)
      (uliftPathReplacementIso_hom_target.{u, v} p) (ULift.up b)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
