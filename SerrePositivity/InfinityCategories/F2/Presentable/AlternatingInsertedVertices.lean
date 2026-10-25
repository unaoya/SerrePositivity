module

public import SerrePositivity.InfinityCategories.F2.Presentable.AlternatingAugmentedStages
public import SerrePositivity.InfinityCategories.F2.Presentable.SplitCoconeIdentityFace
public import SerrePositivity.InfinityCategories.F1B.Cones.SliceIdentityTerminal

/-!
概要：交互次段で挿入される固定標的は、固定標的 slice 内の終対象となる。
方針：挿入された頂点の全増大辺が恒等であることを使う。
規約：全辺の厳密な計算を通して元の恒等錐を回収する。
使われ方：奇数部分列の全関手を定値終対象図式と比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：次の標準交互単体に挿入される固定標的の点。
方針：新しい右の辺の始点を標準単体同型へ送る。
規約：点の射そのものを使う。
使われ方：奇数部分列の頂点の全余錐比較。 -/
def alternatingInsertedPoint (n : ℕ) :
    (Δ[0] : SSet.{u}) ⟶ Δ[2 * (n + 1)] :=
  (SSet.stdSimplex.δ (1 : Fin 2) ≫ joinInr Δ[2 * n] Δ[1]) ≫
    (alternatingSuccessorIso n).hom

/-- 概要：標準交互次段の挿入点からの全増大辺は恒等辺。
方針：標準 join 同型を相殺して、分裂余錐の恒等面を使う。
規約：二点 join 全体の射の等式。
使われ方：固定標的 slice の恒等錐の回収。 -/
lemma standardAlternatingExtensionCocone_inserted_identity
    {C : SSet.{u}} {n : ℕ} {F : (Δ[2 * n] : SSet.{u}) ⟶ C}
    {c d : (sliceUnder F) _⦋0⦌} {e : (sliceUnder F).Edge c d}
    {r : (sliceUnder F).Edge d c} (T : e.CompStruct r (SSet.Edge.id c)) :
    joinMap (alternatingInsertedPoint n) (𝟙 Δ[0]) ≫
      (standardAlternatingExtensionCocone e T).val =
        SSet.const ((sliceUnderProjection F).app (Opposite.op ⦋0⦌) c) := by
  rw [alternatingInsertedPoint, ← Category.comp_id (𝟙 (Δ[0] : SSet.{u})),
    joinMap_comp, Category.assoc, standardAlternatingExtensionCocone_join,
    splitCoconeExtension_inserted_identity]

/-- 概要：交互有限段の元の増大余錐の頂点は元の指定標的。
方針：全右制限を Yoneda 座標へ移す。
規約：頂点そのものの厳密な等式。
使われ方：挿入点の恒等錐の標的の正規化。 -/
lemma AlternatingPresentationStage.augmentation_vertex
    {I : SSet.{u}} {B : SSet.{u + 1}}
    {D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B} {c : JoinCocone D} {n : ℕ}
    (s : AlternatingPresentationStage D c n) :
    JoinCocone.vertex (p := s.diagram) s.augmentation = c.vertex := by
  rw [JoinCocone.vertex_eq, s.augmentation_right, Equiv.apply_symm_apply]

/-- 概要：次段の挿入点の固定標的 slice 内の像は元の恒等錐そのもの。
方針：全増大辺の計算と元の標的頂点の厳密な回収を使う。
規約：slice の実頂点の等式。
使われ方：奇数部分列の頂点の終対象性。 -/
lemma AlternatingPresentationSuccessor.next_inserted_vertex
    {I : SSet.{u}} {B : SSet.{u + 1}}
    {D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B} {c : JoinCocone D} {n : ℕ}
    {s : AlternatingPresentationStage D c n} (t : AlternatingPresentationSuccessor s) :
    SSet.yonedaEquiv (alternatingInsertedPoint n ≫ t.next.sliceDiagram) =
      sliceIdentityCone c.vertex := by
  apply Subtype.ext
  change joinMap (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (alternatingInsertedPoint n)))
    (𝟙 Δ[0]) ≫ (standardAlternatingExtensionCocone t.forward t.triangle).val = _
  rw [Equiv.symm_apply_apply, standardAlternatingExtensionCocone_inserted_identity]
  exact congrArg SSet.const s.augmentation_vertex

/-- 概要：次段の挿入点は固定標的 slice 内の終対象。
方針：元の恒等錐の終対象性を厳密な頂点等式で移す。
規約：関手の全比較には別途点ごとの終対象からの全関手終対象性を使う。
使われ方：奇数部分列の全関手比較の入力。 -/
lemma AlternatingPresentationSuccessor.next_inserted_isTerminal
    {I : SSet.{u}} {B : SSet.{u + 1}} [Quasicategory B]
    {D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B} {c : JoinCocone D} {n : ℕ}
    {s : AlternatingPresentationStage D c n} (t : AlternatingPresentationSuccessor s) :
    IsTerminalVertex (SSet.yonedaEquiv (alternatingInsertedPoint n ≫ t.next.sliceDiagram)) := by
  rw [t.next_inserted_vertex]
  exact F1B.sliceIdentityCone_isTerminalVertex _

end SerrePositivity.InfinityCategories.F2.Presentable
