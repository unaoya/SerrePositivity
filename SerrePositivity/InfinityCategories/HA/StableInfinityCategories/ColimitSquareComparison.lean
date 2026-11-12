module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CosliceSquareDiagram
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CoconeMappingPiZeroChoice
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberComparisonComposition

/-! # Coslice の標準同型による四角形比較

概要：同じ span の余極限余錐間の標準同型は、span を恒等に保つ四角形図式の同型を与える。
方針：coslice から四角形の関手単体集合への射を h に移し、厳密な制限・終点評価の式を使う。
規約：端点の表示変更を含めて Arrow の等号で成分を比較する。
使われ方：colimitVertexIso と suspension の標準比較の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：定値な単体的関手はホモトピー圏の任意の射を恒等射へ送る。
方針：辺の代表元を選び、定値な一次単体を退化した恒等辺と照合する。
規約：端点を含む Arrow の等号で述べる。使われ方：固定した span 上の比較の成分。 -/
lemma stableHoMap_const_arrow {A B : SSet.{u}} [Quasicategory A] (b : B _⦋0⦌)
    {x y : A _⦋0⦌} (f : (SSet.HomotopyCategory.mk x : hoFunctor.obj A) ⟶
      SSet.HomotopyCategory.mk y) :
    Arrow.mk ((hoFunctor.map (SSet.const b : A ⟶ B)).toFunctor.map f) =
      Arrow.mk (𝟙 (SSet.HomotopyCategory.mk b : hoFunctor.obj B)) := by
  obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y f
  have he : e.map ((truncation 2).map (SSet.const b : A ⟶ B)) =
      SSet.Truncated.Edge.id (X := (truncation 2).obj B) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 0) := by
    apply SSet.Truncated.Edge.ext
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback b (SimplexCategory.σ (0 : Fin 1))).symm
  change Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
    (e.map ((truncation 2).map (SSet.const b : A ⟶ B)))) = _
  rw [he]
  have hid := @SSet.Truncated.HomotopyCategory.homMk_id ((truncation 2).obj B)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 0)
  exact (congrArg (fun f => (Arrow.mk f : Arrow (hoFunctor.obj B))) hid).trans (by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    rfl)

/-- 概要：coslice の任意の射の四角形表示は span へ制限すると恒等射。
方針：単体的な制限の定値性と h への合成の計算を使う。
規約：余錐の余極限性は不要。使われ方：標準四角形比較が span を固定することの検査。 -/
lemma cosliceSquareDiagramMap_hom_restriction_arrow {X : SSet.{u}} [Quasicategory X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X) {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    (f : (SSet.HomotopyCategory.mk c : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) ⟶
      SSet.HomotopyCategory.mk d) :
    Arrow.mk ((hoFunctor.map ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app X)).toFunctor.map
      ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap p)).toFunctor.map f)) =
    Arrow.mk (𝟙 (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) :
      hoFunctor.obj ((ihom (horn 2 0 : SSet.{u})).obj X))) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_comp]
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_congr_arrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap_fixed p) f).trans
    (stableHoMap_const_arrow (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) f)

/-- 概要：coslice の射の四角形表示の終端成分は元の終点射影による像。
方針：厳密な終点評価の式を h に移す。
規約：端点の表示変更を含む Arrow の等号。使われ方：標準余極限比較の終点成分。 -/
lemma cosliceSquareDiagramMap_hom_target_arrow {X : SSet.{u}} [Quasicategory X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X) {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    (f : (SSet.HomotopyCategory.mk c : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) ⟶
      SSet.HomotopyCategory.mk d) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map
      ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap p)).toFunctor.map f)) =
    Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)).toFunctor.map f) := by
  change Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1))).toFunctor.map _) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_comp]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_congr_arrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap_targetEvaluation p) f

/-- 概要：coslice の四角形表示の始点評価は固定した span の始点に定値。
方針：span 制限後の始点評価を元の四角形の評価と同定する。
規約：値域に追加仮定なし。使われ方：標準比較の始点成分の恒等性。 -/
lemma cosliceSquareDiagramMap_sourceEvaluation {X : SSet.{u}}
    (p : (horn 2 0 : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0) =
    SSet.const ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.spanSourceEvaluation X).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableSpanPrecomp_sourceEvaluation X, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap_fixed, SSet.const_comp]

/-- 概要：coslice の任意の射の四角形表示の始点成分は固定した始点の恒等射。
方針：始点評価の定値性と h への合成の計算を使う。
規約：端点を含む Arrow の等号。使われ方：suspension の標準比較との照合。 -/
lemma cosliceSquareDiagramMap_hom_source_arrow {X : SSet.{u}} [Quasicategory X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X) {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    (f : (SSet.HomotopyCategory.mk c : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) ⟶
      SSet.HomotopyCategory.mk d) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map
      ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap p)).toFunctor.map f)) =
    Arrow.mk (𝟙 (SSet.HomotopyCategory.mk
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.spanSourceEvaluation X).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) : hoFunctor.obj X)) := by
  change Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0))).toFunctor.map _) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_comp]
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_congr_arrow (cosliceSquareDiagramMap_sourceEvaluation p) f).trans
    (stableHoMap_const_arrow _ f)

/-- 概要：同じ span の余極限余錐の標準同型を四角形の関手圏へ送る。
方針：coslice の標準同型を四角形表示の h の関手で写す。
規約：端点は coslice の頂点の四角形表示。使われ方：suspension 比較との同定。 -/
def colimitSquareComparisonIso {X : SSet.{u}} [Quasicategory X]
    {p : (horn 2 0 : SSet.{u}) ⟶ X} (c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap p)).toFunctor.obj (SSet.HomotopyCategory.mk c) ≅
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap p)).toFunctor.obj (SSet.HomotopyCategory.mk d) :=
  (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap p)).toFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso c d hc hd)

/-- 概要：coslice から得る標準四角形比較の終端成分は colimitVertexIso である。
方針：任意の射に対する終端成分の計算を標準同型へ適用する。
規約：端点の表示変更を含む Arrow の等号。使われ方：二種類の余極限比較の同定。 -/
lemma colimitSquareComparisonIso_target_arrow {X : SSet.{u}} [Quasicategory X]
    {p : (horn 2 0 : SSet.{u}) ⟶ X} (c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map
      (colimitSquareComparisonIso c d hc hd).hom) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso c d hc hd).hom :=
  cosliceSquareDiagramMap_hom_target_arrow p (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso c d hc hd).hom

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
