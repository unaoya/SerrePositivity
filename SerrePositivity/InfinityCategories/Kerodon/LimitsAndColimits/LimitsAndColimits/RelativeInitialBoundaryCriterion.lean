module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeInitialBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IntervalMappingContractible
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulBoundary

/-!
概要：inner fibration の相対始対象性と厳密な始点境界充填の同値。
方針：標準単体への底変換で最初の頂点の始対象性を反映して境界を充填する。
規約：写像空間の相対始対象性は指定した始点についてだけ要求する。
使われ方：標準の U 余極限から操作的な相対充填条件へ戻す判定。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：始対象から出る右 pinched 写像空間は可縮。
方針：区間模型の可縮性を右 pinched 模型との比較同値で戻す。
規約：X は quasicategory。
使われ方：右模型で定義した相対始対象性による始対象性の反映。 -/
lemma kanInitialVertex_pinchedHom_isContractibleKan {X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence x y).choose.isContractibleKan_iff.mpr
    (hx.intervalMappingSpace_isContractibleKan y)

/-- 概要：全ての出る右 pinched 写像空間が可縮なら指定頂点は始対象。
方針：右模型の可縮性を区間模型へ移して始対象性を検出する。
規約：X は quasicategory。
使われ方：標準単体への底変換での相対始対象性の反映。 -/
lemma kanIsInitialVertex_of_pinchedHom_isContractibleKan {X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) (hx : ∀ y : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_of_intervalMappingSpace_isContractibleKan
  intro y
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence x y).choose.isContractibleKan (hx y)

/-- 概要：相対始対象の像が始対象なら元の頂点も始対象。
方針：各写像空間の可縮性を比較のホモトピー同値で反映する。
規約：射 U の充填性は要求しない。
使われ方：標準単体の最初の頂点の始対象性の反映。 -/
lemma KanRelativeInitialVertex.reflects_isInitialVertex {D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] {U : D ⟶ E} {x : D _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex U x)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (U.app (Opposite.op ⦋0⦌) x)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x := by
  apply kanIsInitialVertex_of_pinchedHom_isContractibleKan
  intro y
  exact (hx y).isContractibleKan_iff.mpr (kanInitialVertex_pinchedHom_isContractibleKan hi _)

/-- 概要：標準単体の最初の頂点は始対象。
方針：出る写像空間は各次数で高々一点で、標準辺により非空。
規約：全ての次元の標準単体を扱う。
使われ方：相対始対象性からの厳密な境界充填。 -/
lemma kanStdSimplex_first_isInitialVertex (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (X := (Δ[n] : SSet.{u})) (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) := by
  apply kanIsInitialVertex_of_pinchedHom_isContractibleKan
  intro a
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isContractibleKan_of_nonempty_of_degreewise_subsingleton
  · refine ⟨⟨stdSimplex.edge.{u} n 0 (stdSimplex.obj₀Equiv a) (Fin.zero_le _), ?_, ?_⟩⟩
    · apply stdSimplex.ext
      intro i
      fin_cases i
      rfl
    · apply stdSimplex.ext
      intro i
      fin_cases i
      rfl
  · intro m
    infer_instance

/-- 概要：inner fibration の相対始対象は厳密な始点境界充填を持つ。
方針：標準単体上に引き戻し、最初の頂点の始対象性を反映して全境界を充填する。
規約：射全体の充満忠実性は不要。
使われ方：相対普遍性を厳密な境界固定の構成へ戻す。 -/
lemma kanInitialBoundaryLifting_of_relativeInitial {D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    (x : D _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex U x) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting U x := by
  intro n a b hfirst sq
  let q := pullback.snd U b
  have : InnerFibration q := ⟨innerFibrations.pullback_snd U b (InnerFibration.mem (q := U))⟩
  have : Quasicategory (pullback U b) := quasicategory_of_innerFibration q
  let a' := pullback.lift a (boundary (n + 1)).ι sq.w
  have ha' : a' ≫ q = (boundary (n + 1)).ι := pullback.lift_snd _ _ _
  let t := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ a')
  have htx : (pullback.fst U b).app (Opposite.op ⦋0⦌) t = x := by
    rw [← SSet.yonedaEquiv_comp, Category.assoc, pullback.lift_fst, hfirst,
      Equiv.apply_symm_apply]
  have htq : q.app (Opposite.op ⦋0⦌) t = stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)) := by
    rw [← SSet.yonedaEquiv_comp, Category.assoc, ha', _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι,
      Equiv.apply_symm_apply]
  have htU : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex U ((pullback.fst U b).app (Opposite.op ⦋0⦌) t) := by
    rw [htx]
    exact hx
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex t := (htU.pullback_snd U b t).reflects_isInitialVertex (by
    rw [htq]
    exact kanStdSimplex_first_isInitialVertex (n + 1))
  obtain ⟨F, hF⟩ := ht n a' (SSet.yonedaEquiv.symm_apply_apply _).symm
  have hFq : F ≫ q = 𝟙 Δ[n + 1] := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_of_subcomplex_vertices (boundary (n + 1))
      (fun v ↦ by
        have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v)
        rw [Equiv.symm_apply_apply] at h
        exact h)
    rw [← Category.assoc, hF, ha', Category.comp_id]
  refine ⟨F ≫ pullback.fst U b, ?_, ?_⟩
  · rw [← Category.assoc, hF]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (F ≫ q) ≫ b = b
    rw [hFq, Category.id_comp]

/-- 概要：inner fibration の相対始対象性と始点境界充填は同値。
方針：写像空間への移送と標準単体上での反映を組み合わせる。
規約：D と E は quasicategory。
使われ方：標準の相対普遍性と操作的な構成の共通界面。 -/
lemma kanRelativeInitialVertex_iff_initialBoundary {D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U] (x : D _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex U x ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting U x :=
  ⟨kanInitialBoundaryLifting_of_relativeInitial U x,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeInitialVertex_of_initialBoundary U x⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
