module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiberMaps

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftScaffold
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.VertexFiberNervePullback
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementBaseChange

/-!
概要：通常の圏の関手による left scaffold の底変換。
方針：比較射を引き戻しへ持ち上げ、各係数値の比較を fiber の標準同型で元へ戻す。
規約：底変換は pullback.snd p (nerveMap H) とする。
使われ方：Kerodon Remark 5.3.2.3（Tag 035X）、Theorem 5.3.5.7（Tag 037Q）、底の各標準単体上への還元。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：left fibration の通常の nerve の関手による引き戻しは left fibration。
方針：左ホーンの右持ち上げ性の底変換での閉性を使う。
規約：射影は引き戻しの第二射影。
使われ方：Kerodon §5.1.4（Tag 01U9）、scaffold の底変換の値域。 -/
instance leftFibration_nervePullback
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (H : D ⥤ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p (nerveMap H)) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p (nerveMap H) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

/-- 概要：底変換した比較射は新しい底の nerve 上の射。
方針：引き戻しの持ち上げの第二射影の計算則を使う。
規約：底変換した係数図式は H⋙F。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、単体上の scaffold の底の条件。 -/
lemma leftScaffoldBaseChange_projection
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E)
    (h : l ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) (H : D ⥤ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldBaseChange p F l h H ≫ pullback.snd p (nerveMap H) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (H ⋙ F) := pullback.lift_snd _ _ _

/-- 概要：底変換した比較射の fiber 射は標準 fiber 同型を通すと元の係数の比較射となる。
方針：元の全空間への包含で比較し、引き戻しの第一射影と定値包含の自然性を計算する。
規約：fiber の同型は nerve の頂点の表示も揃える標準同型。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、底変換した scaffold の同値条件。 -/
lemma leftScaffoldBaseChange_fiber
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E)
    (h : l ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) (H : D ⥤ C) (d : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldFiberMap (pullback.snd p (nerveMap H)) (H ⋙ F) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldBaseChange p F l h H)
        (leftScaffoldBaseChange_projection p F l h H) d ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiberNervePullbackIso p H d).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldFiberMap p F l h (H.obj d) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiberNervePullbackIso_hom_ι, ← Category.assoc]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift (H ⋙ F) d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldBaseChange p F l h H) ≫
      pullback.fst p (nerveMap H) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift F (H.obj d) ≫ l
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldBaseChange]
  rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift_baseMap]

/-- 概要：left scaffold の条件は通常の関手による底変換で保存される。
方針：係数値の fiber 比較の可換式と標準 fiber 同型を使い、同値の二三性で判定する。
規約：係数値は Kan、射影は left fibration。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、底を通常の有限順序へ還元する操作。 -/
lemma IsLeftScaffold.baseChange
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    {p : E ⟶ nerve C} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {F : C ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)]
    {l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E} (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.IsLeftScaffold p F l) (H : D ⥤ C) :
    ∃ h : l ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F,
      @_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.IsLeftScaffold D _ _ (pullback.snd p (nerveMap H)) inferInstance (H ⋙ F)
        (fun d ↦ inferInstanceAs (KanComplex (F.obj (H.obj d))))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldBaseChange p F l h H) := by
  have (d : D) : KanComplex ((H ⋙ F).obj d) :=
    inferInstanceAs (KanComplex (F.obj (H.obj d)))
  rcases hs with ⟨h, hf⟩
  refine ⟨h, leftScaffoldBaseChange_projection p F l h H, fun d ↦ ?_⟩
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiberNervePullbackIso p H d)).isQCatEquivalence
  apply he.cancel_right
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldFiberMap (pullback.snd p (nerveMap H)) (H ⋙ F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldBaseChange p F l h H) (leftScaffoldBaseChange_projection p F l h H) d ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiberNervePullbackIso p H d).hom)
  rw [leftScaffoldBaseChange_fiber]
  exact hf (H.obj d)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
