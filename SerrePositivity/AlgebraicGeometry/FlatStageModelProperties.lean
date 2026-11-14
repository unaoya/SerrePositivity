module

public import SerrePositivity.AlgebraicGeometry.FlatStageModelLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
概要：平坦側の実際の模型の図式に、射の性質と qcqs 性を渡す。
方針：各段の射と遷移射の Cartesian な正方形による底変換を使う。
規約：既存構成の性質の移送。平坦被覆 q に固有性は要求しない。
使われ方：A07 の有限段の全射性の比較と、元の X への因子化。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {J : Type u} [SmallCategory J]

/-- 固定した射の平坦性を、各段の被覆の射へ渡す。 -/
instance flatStageModelProjection_flat (D : J ⥤ Scheme.{u}) (i : J)
    {T Y Z : Scheme.{u}} (r : T ⟶ D.obj i) (β : T ⟶ Y) (q : Z ⟶ Y)
    [Flat q] (j : Over i) : Flat ((flatStageModelProjection D i r β q).app j) := by
  change Flat (pullback.fst (pullback.snd (D.map j.hom) r ≫ β) q)
  exact MorphismProperty.pullback_fst _ q ‹Flat q›

/-- 固定した射の局所有限表示性を、各段の被覆の射へ渡す。 -/
instance flatStageModelProjection_locallyOfFinitePresentation (D : J ⥤ Scheme.{u}) (i : J)
    {T Y Z : Scheme.{u}} (r : T ⟶ D.obj i) (β : T ⟶ Y) (q : Z ⟶ Y)
    [LocallyOfFinitePresentation q] (j : Over i) :
    LocallyOfFinitePresentation ((flatStageModelProjection D i r β q).app j) := by
  change LocallyOfFinitePresentation (pullback.fst (pullback.snd (D.map j.hom) r ≫ β) q)
  exact MorphismProperty.pullback_fst _ q ‹LocallyOfFinitePresentation q›

/-- 固定した射の準コンパクト性を、各段の被覆の射へ渡す。 -/
instance flatStageModelProjection_quasiCompact (D : J ⥤ Scheme.{u}) (i : J)
    {T Y Z : Scheme.{u}} (r : T ⟶ D.obj i) (β : T ⟶ Y) (q : Z ⟶ Y)
    [QuasiCompact q] (j : Over i) : QuasiCompact ((flatStageModelProjection D i r β q).app j) := by
  change QuasiCompact (pullback.fst (pullback.snd (D.map j.hom) r ≫ β) q)
  exact MorphismProperty.pullback_fst _ q ‹QuasiCompact q›

/-- 固定した射の準分離性を、各段の被覆の射へ渡す。 -/
instance flatStageModelProjection_quasiSeparated (D : J ⥤ Scheme.{u}) (i : J)
    {T Y Z : Scheme.{u}} (r : T ⟶ D.obj i) (β : T ⟶ Y) (q : Z ⟶ Y)
    [QuasiSeparated q] (j : Over i) : QuasiSeparated ((flatStageModelProjection D i r β q).app j) := by
  change QuasiSeparated (pullback.fst (pullback.snd (D.map j.hom) r ≫ β) q)
  exact MorphismProperty.pullback_fst _ q ‹QuasiSeparated q›

/-- 固定した射の affine 性を、各段の被覆の射へ渡す。 -/
instance flatStageModelProjection_isAffineHom (D : J ⥤ Scheme.{u}) (i : J)
    {T Y Z : Scheme.{u}} (r : T ⟶ D.obj i) (β : T ⟶ Y) (q : Z ⟶ Y)
    [IsAffineHom q] (j : Over i) : IsAffineHom ((flatStageModelProjection D i r β q).app j) := by
  change IsAffineHom (pullback.fst (pullback.snd (D.map j.hom) r ≫ β) q)
  exact MorphismProperty.pullback_fst _ q ‹IsAffineHom q›

/-- 元の affine な遷移射の、二段の底変換も affine。 -/
instance flatStageModelDiagram_isAffineHom_map (D : J ⥤ Scheme.{u}) (i : J)
    {T Y Z : Scheme.{u}} (r : T ⟶ D.obj i) (β : T ⟶ Y) (q : Z ⟶ Y)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {j k : Over i} (f : j ⟶ k) :
    IsAffineHom ((flatStageModelDiagram D i r β q).map f) :=
  MorphismProperty.of_isPullback
    (isPullback_flatStageModelDiagram_map D i r β q f).flip inferInstance

/-- 二つの準コンパクトな射による図式の各段は準コンパクト。 -/
instance flatStageModelDiagram_compactSpace (D : J ⥤ Scheme.{u}) (i : J)
    {T Y Z : Scheme.{u}} (r : T ⟶ D.obj i) (β : T ⟶ Y) (q : Z ⟶ Y)
    [∀ j, CompactSpace (D.obj j)] [QuasiCompact r] [QuasiCompact q] (j : Over i) :
    CompactSpace ((flatStageModelDiagram D i r β q).obj j) := by
  haveI : CompactSpace ((stageBaseChangeDiagram D i r).obj j) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace ((flatStageModelProjection D i r β q).app j)

/-- 二つの準分離な射による図式の各段は準分離。 -/
instance flatStageModelDiagram_quasiSeparatedSpace (D : J ⥤ Scheme.{u}) (i : J)
    {T Y Z : Scheme.{u}} (r : T ⟶ D.obj i) (β : T ⟶ Y) (q : Z ⟶ Y)
    [∀ j, QuasiSeparatedSpace (D.obj j)] [QuasiSeparated r] [QuasiSeparated q] (j : Over i) :
    QuasiSeparatedSpace ((flatStageModelDiagram D i r β q).obj j) := by
  haveI : QuasiSeparatedSpace ((stageBaseChangeDiagram D i r).obj j) := inferInstance
  exact quasiSeparatedSpace_of_quasiSeparated ((flatStageModelProjection D i r β q).app j)

end SerrePositivity.AlgebraicGeometry
