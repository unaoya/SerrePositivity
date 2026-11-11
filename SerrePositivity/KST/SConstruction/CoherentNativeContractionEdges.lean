module
public import SerrePositivity.KST.SConstruction.CoherentArrowNativeFamilies
public import SerrePositivity.KST.SConstruction.CoherentHomotopyComponentCalculus

/-! # 元の全合成列の native 収縮の成分辺を回収する
概要：元の収縮の各成分が、二端点の精密化から全頂点 Path への元の包含辺を評価したものと示す。
方針：通常の初対象からの自然変換の成分と、精密化の一単体の Path flag を照合する。
規約：実円柱の成分辺を保持し、ホモトピー類の代表を選び直さない。
使われ方：元の K の二円柱の指定頂点を、既存 BF 境界の二三角形へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] {x y : I} {f : x ⟶ y}

/-- 元の精密化の像の Path から、同じ最終列の全頂点 Path への指定包含。 -/
def coherentStringRefinementPathToFull {s t : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f} (a : s ⟶ t) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringRefinementPath a ⟶ coherentStringFullPath t :=
  ⟨⟨⟨fun _ _ => Set.mem_univ _⟩⟩⟩

/-- 元の精密化の辺の Path flag は、元の像の Path から全頂点 Path への包含辺。 -/
lemma coherentStringPathFlag_arrow {s t : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f} (a : s ⟶ t) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathFlag (nerve.edgeMk a).edge =
      (nerve.edgeMk (coherentStringRefinementPathToFull a)).edge := by
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · rfl
  · exact coherentStringRefinementPath_id t
  · apply InducedCategory.hom_ext
    exact Subsingleton.elim _ _

/-- 元の native 収縮の各成分は、同じ元の精密化 Path の包含辺の実評価。 -/
lemma coherentArrowNativeContraction_vertex_edge
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C)
    (f : x ⟶ y) (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (coherentArrowNativeContraction Q f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s)).edge =
      (coherentStringNativeMap Q s).app (Opposite.op ⦋1⦌)
        (nerve.edgeMk (coherentStringRefinementPathToFull (coherentArrowStringDirectTo s))).edge := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.ordinaryComparisonHomotopy_vertex (coherentArrowStringContractionTransformation f) s
  have hm := congrArg ((coherentArrowNativeFamily Q f).app (Opposite.op ⦋1⦌)) h
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (coherentArrowNativeContraction Q f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s)).edge =
    (coherentStringNativeMap Q s).app _ _ at hm
  exact hm.trans (congrArg ((coherentStringNativeMap Q s).app (Opposite.op ⦋1⦌))
    (coherentStringPathFlag_arrow (coherentArrowStringDirectTo s)))

/-- 前合成した元の円柱の成分は、元の円柱の同じ像の頂点の成分辺である。 -/
lemma coherentHomotopyVertexEdge_precomp {A B X : SSet.{u}} {f g : B ⟶ X}
    (H : SSet.Homotopy f g) (i : A ⟶ B) (a : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H i) a).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (i.app (Opposite.op ⦋0⦌) a)).edge := by
  change H.h.app (Opposite.op ⦋1⦌)
    (i.app (Opposite.op ⦋1⦌) (A.σ 0 a), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
    H.h.app (Opposite.op ⦋1⦌)
      (B.σ 0 (i.app (Opposite.op ⦋0⦌) a), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
  exact congrArg (fun z => H.h.app (Opposite.op ⦋1⦌) (z, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge))
    (NatTrans.naturality_apply i (SimplexCategory.σ (0 : Fin 1)).op a)

/-- パラメータの制限と標的の表示変更を行っても、元の成分の Path 包含辺を保持する。 -/
lemma coherentArrowNativeContraction_prepost_vertex_edge
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C)
    (f : x ⟶ y) {U E : SSet.{u}} (i : U ⟶ nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f))
    (q : SimplicialCategory.sHom (coherentStringVertexObject Q x)
      (coherentStringVertexObject Q y) ⟶ E)
    (a : U _⦋0⦌) (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) (hv : i.app (Opposite.op ⦋0⦌) a = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (coherentArrowNativeContraction Q f) i) q) a).edge =
      q.app (Opposite.op ⦋1⦌) ((coherentStringNativeMap Q s).app (Opposite.op ⦋1⦌)
        (nerve.edgeMk (coherentStringRefinementPathToFull (coherentArrowStringDirectTo s))).edge) := by
  have hp := coherentHomotopyVertexEdge_precomp (coherentArrowNativeContraction Q f) i a
  have hq := congrArg (fun a => (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
    (coherentArrowNativeContraction Q f) a).edge) hv
  have h := coherentArrowNativeContraction_vertex_edge Q f s
  exact congrArg (q.app (Opposite.op ⦋1⦌)) (hp.trans (hq.trans h))

end SerrePositivity.KST.SConstruction
