module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiberMaps

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.BaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.VertexFiberNervePullback
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementBaseChange

/-!
概要：通常の圏の関手による cocartesian scaffold の底変換。
方針：比較射を引き戻しへ持ち上げ、各係数値の比較を fiber の標準同型で元へ戻す。
規約：底変換は pullback.snd p (nerveMap H) とする。
使われ方：Kerodon Remark 5.3.2.3（Tag 035X）、Theorem 5.3.5.7（Tag 037Q）、底の各標準単体上への還元。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories

/-- 概要：底変換した比較射は新しい底の nerve 上の射。
方針：引き戻しの持ち上げの第二射影の計算則を使う。
規約：底変換した係数図式は H⋙F。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、単体上の scaffold の底の条件。 -/
lemma cocartesianScaffoldBaseChange_projection
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E)
    (h : l ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) (H : D ⥤ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldBaseChange p F l h H ≫ pullback.snd p (nerveMap H) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (H ⋙ F) := pullback.lift_snd _ _ _

/-- 概要：底変換した比較射の fiber 射は標準 fiber 同型を通すと元の係数の比較射となる。
方針：元の全空間への包含で比較し、引き戻しの第一射影と定値包含の自然性を計算する。
規約：fiber の同型は nerve の頂点の表示も揃える標準同型。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、底変換した scaffold の同値条件。 -/
lemma cocartesianScaffoldBaseChange_fiber
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E)
    (h : l ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) (H : D ⥤ C) (d : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldFiberMap (pullback.snd p (nerveMap H)) (H ⋙ F) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldBaseChange p F l h H)
        (cocartesianScaffoldBaseChange_projection p F l h H) d ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiberNervePullbackIso p H d).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldFiberMap p F l h (H.obj d) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiberNervePullbackIso_hom_ι, ← Category.assoc]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift (H ⋙ F) d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldBaseChange p F l h H) ≫
      pullback.fst p (nerveMap H) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift F (H.obj d) ≫ l
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldBaseChange]
  rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift_baseMap]

/-- 概要：replacement の水平辺は底の関手による写像で水平辺に移る。
方針：長さ一の射列の後合成と、その始点の定値係数を計算する。
規約：底の関手の忠実性や充填性は不要。
使われ方：底変換した scaffold の cocartesian 条件。 -/
lemma cocartesianScaffoldHorizontalEdge_baseMap
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) {c d : D} (f : c ⟶ d)
    (x : (F.obj (H.obj c)) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementBaseMap H F).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianScaffoldHorizontalEdge (H ⋙ F) f x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianScaffoldHorizontalEdge F (H.map f) x := by
  have hσ : ComposableArrows.mk₁ f ⋙ H = ComposableArrows.mk₁ (H.map f) :=
    ComposableArrows.ext₁ rfl rfl (by simp)
  exact Sigma.ext hσ (HEq.rfl)

/-- 概要：底変換に現れる頂点 fiber は quasicategory。
方針：inner fibration の頂点 fiber の充填性を使う。
規約：同値の型を述べるための局所 instance。
使われ方：底変換された scaffold の fiber 条件。 -/
local instance {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p] (v : B _⦋0⦌) :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p v) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiber_quasicategory_of_innerFibration p v

/-- 概要：cocartesian scaffold の三条件は任意の通常の関手による底変換で保たれる。
方針：水平辺の像を元の scaffold に戻し、fiber 条件を標準 fiber 同型で移す。
規約：係数値は quasicategory であり、Kan 性は要求しない。
使われ方：一般の scaffold の全空間比較を有限鎖上へ還元する。 -/
lemma CocartesianScaffold.baseChange
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    {p : E ⟶ nerve C} [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] {F : C ⥤ SSet.{u}}
    [∀ c, Quasicategory (F.obj c)] {l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E}
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianScaffold p F l) (H : D ⥤ C) :
    @_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianScaffold D _ _ (pullback.snd p (nerveMap H)) inferInstance (H ⋙ F)
      (fun d ↦ inferInstanceAs (Quasicategory (F.obj (H.obj d))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldBaseChange p F l hs.projection H) := by
  have (d : D) : Quasicategory ((H ⋙ F).obj d) :=
    inferInstanceAs (Quasicategory (F.obj (H.obj d)))
  refine ⟨cocartesianScaffoldBaseChange_projection p F l hs.projection H, ?_, fun d ↦ ?_⟩
  · intro c d f x
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_pullback p (nerveMap H)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldBaseChange p F l hs.projection H ≫ pullback.fst p (nerveMap H)).app _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianScaffoldHorizontalEdge (H ⋙ F) f x))
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldBaseChange p F l hs.projection H ≫ pullback.fst p (nerveMap H) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementBaseMap H F ≫ l := pullback.lift_fst _ _ _
    rw [he]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (l.app (Opposite.op ⦋1⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementBaseMap H F).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianScaffoldHorizontalEdge (H ⋙ F) f x)))
    rw [cocartesianScaffoldHorizontalEdge_baseMap]
    exact hs.horizontal (H.map f) x
  · have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiberNervePullbackIso p H d)).isQCatEquivalence
    apply he.cancel_right
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldFiberMap (pullback.snd p (nerveMap H)) (H ⋙ F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldBaseChange p F l hs.projection H)
      (cocartesianScaffoldBaseChange_projection p F l hs.projection H) d ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiberNervePullbackIso p H d).hom)
    rw [cocartesianScaffoldBaseChange_fiber]
    exact hs.fiber (H.obj d)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
