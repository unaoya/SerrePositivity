module
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BoundaryTensor
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.AdjunctionHom
public import SerrePositivity.HomotopicalAlgebra.Quillen.Saturation
public import SerrePositivity.HomotopicalAlgebra.Simplicial.FiniteTensorAdjunction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveStandard
public import SerrePositivity.HomotopicalAlgebra.Simplicial.StandardSimplexCosimplicialHom
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.FiniteTensorAdjunction


/-!
# 単体集合モデルを仮定しない左随伴の標準 frame

概要：Hovey §5 の標準単体による frame を単射と anodyne の保存から構成する。
方針：有限境界の余極限表示と標準単体の実際の収縮を使う。
規約：モデル構造は値圏だけに置き、単体集合のモデル構造は入力しない。
使われ方：重み付き錐空間と計算対象への導来 Hom の比較。
-/

@[expose] public section

noncomputable section

universe u v

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

open CategoryTheory Limits HomotopicalAlgebra
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex

variable {C : Type v} [Category.{u} C] [ModelCategory C]
  (F : SSet.{u} ⥤ C) [F.IsLeftAdjoint]
  (hmono : ∀ {X Y : SSet.{u}} (i : X ⟶ Y), Mono i → cofibrations C (F.map i))
  (hanodyne : ∀ {X Y : SSet.{u}} (i : X ⟶ Y),
    SSet.anodyneExtensions i → weakEquivalences C (F.map i))

include hmono

/-- 概要：標準単体の左随伴像は Reedy cofibrant（Hovey §5）。
方針：境界の有限表示を保存し、境界包含の像の cofibration 性を移す。
規約：単体集合の単射の保存だけを使う。
使われ方：重み付き実現から構成する frame の cofibrancy。 -/
lemma reedyCofibrant :
    reedyLeft simplex (cofibrations C) (initial.to (SSet.stdSimplex ⋙ F)) := by
  intro j
  induction j using SimplexCategory.rec with | _ n =>
  apply ((cofibrations C).arrow_iso_iff
    (latchingInitialArrowIso simplex (SimplexCategory.mk n) (SSet.stdSimplex ⋙ F))).mp
  apply ((cofibrations C).arrow_iso_iff
    (boundaryTensorArrowIso (SSet.stdSimplex ⋙ F) n)).mp
  rw [← _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.tensorIso_inclusion F (SSet.boundary n)]
  exact (cofibrations C).comp_mem _ _
    ((cofibrations C).of_isIso (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.tensorIso F (SSet.boundary n).toSSet).hom)
    (hmono _ inferInstance)

omit hmono
include hanodyne

omit [F.IsLeftAdjoint] in
/-- 概要：標準単体の左随伴像は homotopically constant（Hovey §5）。
方針：anodyne を反転する局所化で標準単体の終射を反転し、モデルの飽和性を使う。
規約：幾何的弱同値と単体集合モデルの同定は不要。
使われ方：構成した標準 frame の全単体作用素の弱同値性。 -/
lemma homotopicallyConstant {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences C ((SSet.stdSimplex ⋙ F).map f) := by
  let Q := (weakEquivalences C).Q
  have hQ : SSet.anodyneExtensions.IsInvertedBy (F ⋙ Q) := by
    intro X Y i hi
    exact Localization.inverts Q (weakEquivalences C) _ (hanodyne i hi)
  have hterm (j : SimplexCategory) :
      IsIso ((F ⋙ Q).map (SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj j))) := by
    induction j using SimplexCategory.rec with | _ k =>
    exact SimplicialModel.SimplexNerve.standardTerminal_isIso (F ⋙ Q) hQ k
  have := hterm m
  have := hterm n
  have he : (F ⋙ Q).map (SSet.stdSimplex.map f) ≫
      (F ⋙ Q).map (SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj m)) =
      (F ⋙ Q).map (SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj n)) := by
    rw [← Functor.map_comp]
    exact congrArg (F ⋙ Q).map (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
  have : IsIso ((F ⋙ Q).map (SSet.stdSimplex.map f)) := by
    apply (isIso_comp_right_iff _ ((F ⋙ Q).map
      (SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj m)))).mp
    rw [he]
    infer_instance
  exact (SerrePositivity.Quillen.weakEquivalences_iff_isIso_map Q _).mpr this

omit hanodyne

/-- 概要：標準 frame の実際の Hom は左随伴の右随伴と同型（Hovey §5）。
方針：通常の随伴の Hom 同型と標準単体の Yoneda 同型を合成する。
規約：全単体と終域の射に自然な単体集合の同型。
使われ方：重み付き錐空間と frame Hom の π₀ の照合。 -/
def homIso {R : C ⥤ SSet.{u}} (adj : F ⊣ R) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (SSet.stdSimplex ⋙ F) ≅ R :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.adjunctionHomIsoSameUniverse adj SSet.stdSimplex ≪≫
    Functor.isoWhiskerLeft R QuillenStandardFrame.homIso ≪≫ Functor.rightUnitor R

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
