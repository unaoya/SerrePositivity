module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.GlobalDiagramFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinPointwiseExistence

/-!
概要：全空間上の一つの図式の fiber ごとの余極限から普遍余錐の族を作る。
方針：通常の制限の余極限を族の頂点の相対始対象へ移し、coherent な族へ組み立てる。
規約：各 fiber の他の図式の余極限は要求しない。
使われ方：任意の関手の oriented comma への置き換えから Kan 拡張を構成する。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：全空間の図式の fiber での余極限は族の同じ頂点に相対始対象を与える。
方針：余錐の fiber の同型と制限の可換性、図式の族の頂点の同定を使う。
規約：一つの指定された fiber の図式だけを仮定する。
使われ方：普遍余錐の coherent な族の各頂点での存在。 -/
lemma exists_kanGlobalColimit_initial_vertex {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (F : K ⟶ D) (c : C _⦋0⦌) (hcol : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c ≫ F)) :
    ∃ x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) D) _⦋0⦌,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p)).app (Opposite.op ⦋0⦌) x =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily p F).app (Opposite.op ⦋0⦌) c ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p)) x := by
  obtain ⟨z, hz⟩ := hcol
  let x := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinCoconeFiberIso p c D).hom.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex z.val)
  refine ⟨x.val, ?_, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinCocone_initialBoundary p c hz⟩
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinCoconeFiberIso_restriction (D := D) p c)
      (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex z.val)
  have hzv : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) D).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex z.val) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c ≫ F) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) Δ[0] ≫ z.val) = _
    rw [z.property]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPreFiber (D := D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p) c).app
    (Opposite.op ⦋0⦌) x = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberIso p c D).hom.app
      (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) D).app
        (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex z.val)) at h
  rw [hzv] at h
  exact (congrArg Subtype.val h).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily_fiber_vertex p F c)

/-- 概要：fiber ごとに必要な余極限があれば普遍余錐の族を選べる。
方針：各頂点の相対始対象の存在から相対始対象全体の引き戻しの切断を作る。
規約：元の図式を厳密に制限として保つ。
使われ方：相対 join 上の図式を uncurry するための族。 -/
lemma exists_kanGlobalColimit_initial_family {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (F : K ⟶ D) (hcol : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c ≫ F)) :
    ∃ l : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) D,
      l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily p F ∧
        ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p))
            (l.app (Opposite.op ⦋0⦌) c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeInitial_family_of_vertices _ _
    (fun c ↦ exists_kanGlobalColimit_initial_vertex p F c (hcol c))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
