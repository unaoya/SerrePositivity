module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.OverOpposite
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.UnderIso
public import SerrePositivity.InfinityCategories.F1B.Cones.SliceProjectionLaws

/-!
概要：通常の Over の nerve と元の頂点上の native な slice を同型にする。
方針：Under の比較を反転し標的と零単体の固定図式を正規化する。
規約：同じ宇宙の小さい圏を扱う。
使われ方：B5 の左 Kan の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet Opposite
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {C : Type u} [Category.{u} C] (c : C)

/-- 概要：Over の nerve を反転した点図式上の slice へ写す同型。
方針：Under の nerve の比較と native な coslice の反転を合成する。
規約：反転した標的と点図式をまだ保持する。
使われ方：元の頂点上の slice の同型への中間表示。 -/
def nerveOverRawSliceIso : nerve (Over c) ≅ sliceOver (SSet.opFunctor.map (nervePoint (op c))) :=
  SerrePositivity.InfinityCategories.F1B.nerveOverOppositeUnderIso c ≪≫ SSet.opFunctor.mapIso (SerrePositivity.InfinityCategories.F1B.nerveUnderIso (op c)) ≪≫
    SerrePositivity.InfinityCategories.F1B.sliceUnderOpIso (nervePoint (op c))

/-- 概要：Over の nerve と元の頂点上の native な slice の同型。
方針：標的と点図式を同型で戻し最後の等式で輸送する。
規約：元の指定された頂点 c を固定する。
使われ方：左 Kan の局所添字の古典比較。 -/
def nerveOverIso : nerve (Over c) ≅ sliceOver (nervePoint c) := by
  let p := SSet.opFunctor.map (nervePoint (op c))
  let q := (SerrePositivity.InfinityCategories.F1B.nerveUnopIso C).hom
  have := sliceOverPostcomp_isIso p q
  have := sliceOverRestrict_isIso (p ≫ q) (stdSimplex.opIso ⦋0⦌).inv
  exact nerveOverRawSliceIso c ≪≫ asIso (sliceOverPostcomp p q) ≪≫
    asIso (sliceOverRestrict (p ≫ q) (stdSimplex.opIso ⦋0⦌).inv) ≪≫
      eqToIso (congrArg sliceOver (SerrePositivity.InfinityCategories.F1B.nerveOverBase_eq c))

/-- 概要：中間の slice の同型は標的を戻すと元の忘却射影を与える。
方針：coslice の反転の射影の式と Under の比較を使う。
規約：標的を戻す同型を明記する。
使われ方：最終的な射影の保存の証明。 -/
lemma nerveOverRawSliceIso_projection : (nerveOverRawSliceIso c).hom ≫
    sliceOverProjection (SSet.opFunctor.map (nervePoint (op c))) ≫
      (SerrePositivity.InfinityCategories.F1B.nerveUnopIso C).hom = nerveMap (Over.forget c) := by
  dsimp only [nerveOverRawSliceIso]
  rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc,
    ← Category.assoc (SerrePositivity.InfinityCategories.F1B.sliceUnderOpIso _).hom, SerrePositivity.InfinityCategories.F1B.sliceUnderOpIso_projection]
  change (SerrePositivity.InfinityCategories.F1B.nerveOverOppositeUnderIso c).hom ≫ SSet.opFunctor.map (SerrePositivity.InfinityCategories.F1B.nerveUnderMap (op c)) ≫
    SSet.opFunctor.map (sliceUnderProjection (nervePoint (op c))) ≫ _ = _
  rw [← Category.assoc (SSet.opFunctor.map _), ← SSet.opFunctor.map_comp,
    SerrePositivity.InfinityCategories.F1B.nerveUnderMap_projection]
  exact SerrePositivity.InfinityCategories.F1B.nerveOverOppositeUnderIso_projection c

/-- 概要：Over の nerve と slice の同型は元の忘却射影を厳密に保つ。
方針：反転・制限・後合成の射影の式を順に使う。
規約：単体集合の射の厳密な等式。
使われ方：左 Kan の局所図式の一致。 -/
lemma nerveOverIso_projection : (nerveOverIso c).hom ≫ sliceOverProjection (nervePoint c) =
    nerveMap (Over.forget c) := by
  dsimp only [nerveOverIso]
  simp only [Iso.trans_hom, Category.assoc]
  rw [SerrePositivity.InfinityCategories.F1B.sliceOverProjection_eqTransport (SerrePositivity.InfinityCategories.F1B.nerveOverBase_eq c)]
  erw [SerrePositivity.InfinityCategories.F1B.sliceOverRestrict_projection, SerrePositivity.InfinityCategories.F1B.sliceOverPostcomp_projection]
  rw [← Category.assoc]
  exact nerveOverRawSliceIso_projection c

end SerrePositivity.InfinityCategories.F1B
