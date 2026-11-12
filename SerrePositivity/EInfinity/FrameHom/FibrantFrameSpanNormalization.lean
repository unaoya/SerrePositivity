module

public import SerrePositivity.EInfinity.FrameHom.FibrantFrameSpanComparison
public import SerrePositivity.EInfinity.FrameHom.FrameElementSpans

/-!
概要：全図式による弱比較を元の source frame の同じ三本矢の射へ戻す。
方針：全単体で元の脚と中間射を回収し、固定端点の恒等合成だけを消す。
規約：ホモトピーによる別射への置き換えをしない。
使われ方：元の二列 roof と hammock の実比較の弱同値性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom.FibrantFrameSpanNormalization
open CategoryTheory Limits HomotopicalAlgebra Opposite
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories
open FibrantFrameSpanComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {X : C} (q : CofibrantResolution (C := C) simplex X) (Y : C)

/-- 概要：元の frame の全単体から同じ特殊三本矢への実比較。
方針：左脚は同じ augmentation、右脚は同じ恒等射を使う。
規約：元の射を保つ。使われ方：全図式の比較との厳密な照合。 -/
def comparisonFunctor : (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ ⥤ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y :=
  frameElementSpanFunctor _ _ q.obj q.augmentation (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionAugmentation_trivialFibration q)
    (𝟙 Y) ((trivialCofibrations C).id_mem Y)

/-- 概要：元の全単体の宇宙を揃えて同じ三本矢の nerve に送る。
方針：元の比較関手に同じ down だけを前合成する。
規約：全単体と全作用素。使われ方：実弱比較の元の右射。 -/
def comparisonNerveMap :
    nerve (AsSmall.{max u v} ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ)) ⟶
      nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y) where
  app _ := ↾fun c => c ⋙ AsSmall.down.{0, v, max u v} ⋙ comparisonFunctor q Y
  naturality _ _ _ := rfl

variable [IsFibrant Y]

omit [IsFibrant Y] in
/-- 概要：三本矢の射の全成分の異種等式は元の射の異種等式を与える。
方針：両対象の等式を消去して元の成分外延性へ戻す。
規約：元の射を保つ。使われ方：全単体の自然性の照合。 -/
private lemma hom_hext {S S' T T' : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y} (hs : S = S') (ht : T = T')
    (f : S ⟶ T) (g : S' ⟶ T') (hl : HEq f.left g.left) (hr : HEq f.right g.right) :
    HEq f g := by
  cases hs
  cases ht
  exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext _ _ (eq_of_heq hl) (eq_of_heq hr))

/-- 概要：元の全図式の回収は同じ source frame 比較の実射そのもの。
方針：全射列で元の三射を取り出し、恒等との合成だけを消す。
規約：元の全比較を保持。使われ方：同じ射への弱同値性の輸送。 -/
lemma comparisonNerveMap_fac :
    fibrantSpanNerveMap q Y ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FibrantRightSpans.inclusion X Y) =
      comparisonNerveMap q Y := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  change Fin (n.unop.len + 1) ⥤
    AsSmall.{max u v} (q.obj.op ⋙ yoneda.obj Y).Elementsᵒᵖ at c
  have ho (j : Fin (n.unop.len + 1)) :
      (((fibrantSpanNerveMap q Y ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FibrantRightSpans.inclusion X Y)).app n) c).obj j =
        (((comparisonNerveMap q Y).app n) c).obj j := by
    let s := (comparisonFunctor q Y).obj (AsSmall.down.obj (c.obj j))
    change ({s with
      leftMap := s.leftMap ≫ 𝟙 X
      left_mem := by simpa only [Category.comp_id] using s.left_mem}) = s
    simp only [Category.comp_id]
  apply CategoryTheory.Functor.hext ho
  intro i j h
  apply hom_hext (Y := Y) (ho i) (ho j)
  · dsimp [fibrantSpanNerveMap, spanDiagramNerveMap, resolutionNerveMap, fiberNerveMap,
      recoveryNerveMap, HeterogeneousSmallComma.recoveryNerveMap,
      HeterogeneousSmallComma.grothendieckEquivalence, HeterogeneousSmallComma.equivalence,
      HeterogeneousSmallComma.down, comparisonNerveMap, comparisonFunctor, nerveMap,
      Thomason.selfLiftIso, Thomason.fiberNerveMap, NerveAsSmall.iso,
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FibrantRightSpans.inclusion, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.forget, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.leftSliceForget,
      CategoryTheory.Equivalence.mk, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.equivalence, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.toComma,
      Grothendieck.map, Grothendieck.ι, FibrantRightResolutionDiagram.comparison,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagramPre, CosimplicialHomElements.smallEquivalence,
      CosimplicialHomElements.smallToComma, smallResolutionOverFunctor, resolutionOverFunctor,
      CostructuredArrow.pre, Comma.preLeft, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.AsSmallComma.smallFunctor,
      frameElementSpanFunctor, frameElementSpanMap, AsSmall.up, AsSmall.down]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fromComma_map_left, Category.id_comp]
    change HEq (q.obj.map _) (q.obj.map _)
    apply heq_of_eq
    congr 1
    refine (congrArg ULift.down (CostructuredArrow.comp_left _ _)).trans ?_
    let θ := (AsSmall.down.map (c.map h)).unop.hom.unop
    change _ ≫ θ = θ
    refine (congrArg (fun f : _ ⟶ _ => f ≫ θ) ?_).trans (Category.id_comp θ)
    exact (congrArg ULift.down (CostructuredArrow.eqToHom_left _)).trans rfl
  · rfl

variable (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
include r in
/-- 概要：元の source frame の同じ特殊三本矢比較は弱ホモトピー同値。
方針：同じ全図式の弱比較と fibrant 右脚制限の包含を厳密な因子分解で合成する。
規約：元の標的の fibrancy のみを要求。使われ方：同じ二列 roof 比較の弱同値性。 -/
lemma comparisonNerveMap_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (comparisonNerveMap q Y) := by
  rw [← comparisonNerveMap_fac]
  exact (fibrantSpanNerveMap_isWeakHomotopyEquivalence q Y).comp
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FibrantRightSpans.inclusion_isWeakHomotopyEquivalence r X Y)

end SerrePositivity.EInfinity.FrameHom.FibrantFrameSpanNormalization
