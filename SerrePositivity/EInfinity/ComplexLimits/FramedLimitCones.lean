module

public import SerrePositivity.EInfinity.ComplexLimits.FramedLimit
public import SerrePositivity.EInfinity.ComplexLimits.Probe
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.FrameCones
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.MixedFrameDiagrams
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.Reindex
public import SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroLocalization

/-!
# 実際の 複体の右 frame の Kan 錐空間

概要：BM 命題 4.1・Hovey §5 の右 frame の重み付き錐に擬同型不変性を与える。
方針：試験始域を具体的に cofibrant 置換し、射影 cofibrant 重みの frame Hom を使う。
規約：元の 複体に cofibrancy を仮定せず、単体集合モデルも仮定しない。
使われ方：一般 homotopy 極限の計算対象を写像空間で検証する。
-/

@[expose] public section

noncomputable section

universe u v w

namespace SerrePositivity.EInfinity.ComplexLimits

open CategoryTheory Limits _root_.HomotopicalAlgebra Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.DiagramModel SerrePositivity.Reedy

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：複体図式の右 frame への実際の重み付き錐空間（Hovey §5）。
方針：同じ一点重みと右 frame の Hom の錐を取る。
規約：この段階では計算対象への Map^h との同値を主張しない。
使われ方：一般 homotopy 極限の図式に関する不変性の検出。 -/
def framedLimitConeSpace (Y : (Complex A)) :
    (K ⥤ (Complex A)) ⥤ SSet.{u} := by
  let := projectiveModelCategory A
  exact (rightFrameDiagramFamily A K).rightOp ⋙ FrameWeightRealization.homFamily Kᵒᵖ ⋙
    (CategoryTheory.evaluation (Complex A)ᵒᵖ (Kᵒᵖᵒᵖ ⥤ SSet.{u})).obj
      (op (framedLimitProbe A Y)) ⋙ WeightedCones.coneSpace Kᵒᵖᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)

/-- 概要：選んだ右 frame への重み付き錐空間は Kan 複体（Hovey §5）。
方針：具体的な試験始域の置換と各右 frame の Kan Hom を使う。
規約：元の図式・試験始域に cofibrancy 条件はない。
使われ方：一般 homotopy 極限の実際の Kan 写像空間の比較。 -/
lemma framedLimitConeSpace_kanComplex (F : K ⥤ (Complex A))
    (Y : (Complex A)) : SSet.KanComplex ((framedLimitConeSpace A K Y).obj F) := by
  let := projectiveModelCategory A
  have := framedLimitProbe_cofibrant A Y
  have : IsFibrant (op (framedLimitProbe A Y)) :=
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fibrantOp_of_cofibrant _
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameCone_kanComplex Kᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K) (rightFrameDiagram A K F)
    (fun k => rightFrame_cofibrant A (F.obj k.unop))
    (fun k _ _ f => rightFrame_homotopicallyConstant A (F.obj k.unop) f)
    (op (framedLimitProbe A Y))

/-- 概要：図式の頂点ごとの擬同型は右 frame の錐で反転される（BM §1、Hovey §5）。
方針：実際の右 frame の弱同値保存と自然な Brown 分解を使う。
規約：任意の anodyne 反転先を許し、単体集合モデルの仮定はない。
使われ方：一般 homotopy 極限の擬同型不変性への Hom 比較。 -/
lemma framedLimitConeSpace_map_isIso {F G : K ⥤ (Complex A)} (f : F ⟶ G)
    (hf : ∀ k, QuasiIso (f.app k)) (Y : (Complex A))
    {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    IsIso (L.map ((framedLimitConeSpace A K Y).map f)) := by
  let := projectiveModelCategory A
  have := framedLimitProbe_cofibrant A Y
  have : IsFibrant (op (framedLimitProbe A Y)) :=
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fibrantOp_of_cofibrant _
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameCone_source_weakEquivalence_isIso Kᵒᵖ
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K) L hL (rightFrameFactorization A)
    ((rightFrameDiagramFamily A K).map f.op)
    (fun k => rightFrame_cofibrant A (G.obj k.unop))
    (fun k => rightFrame_cofibrant A (F.obj k.unop))
    (fun k n => rightFrame_map_weakEquivalence A (f.app k.unop) (hf k.unop) n)
    (op (framedLimitProbe A Y))

/-- 概要：図式の擬同型は右 frame の錐の連結成分を全単射にする（Hovey §5）。
方針：anodyne を反転する実際の π₀ 関手へ不変性を適用する。
規約：元の錐空間の同じ射が誘導する連結成分の写像を使う。
使われ方：一般 homotopy 極限の局所化 Hom の比較。 -/
lemma framedLimitConeSpace_map_piZero_bijective {F G : K ⥤ (Complex A)}
    (f : F ⟶ G) (hf : ∀ k, QuasiIso (f.app k)) (Y : (Complex A)) :
    Function.Bijective (SSet.mapπ₀ ((framedLimitConeSpace A K Y).map f)) := by
  have h := framedLimitConeSpace_map_isIso A K f hf Y SSet.π₀Functor
    SimplicialModel.PiZeroLocalization.inverts_anodyne
  exact (CategoryTheory.isIso_iff_bijective _).mp h

end SerrePositivity.EInfinity.ComplexLimits
