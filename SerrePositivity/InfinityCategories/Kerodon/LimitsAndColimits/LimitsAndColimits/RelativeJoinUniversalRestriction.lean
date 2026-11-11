module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinFunctorMappingSpace
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.GlobalColimitFiberAssembly
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulBoundary

/-!
概要：fiber ごとに普遍な相対 join 図式の全部分 ∞ 圏から元の図式への制限。
方針：通常の制限の写像空間の同値を全部分圏へ制限し、局所余極限の存在で頂点を持ち上げる。
規約：充満忠実性には余極限の存在を仮定しない。
使われ方：Kan 拡張の図式の ∞ 圏としての普遍性と coherent な選択。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：関手の頂点が全ての fiber で普遍な余錐を与える条件。
方針：関手頂点を実際の図式に戻して fiber の余錐を評価する。
規約：相対 join の右端を固定しない。
使われ方：普遍な相対 join 図式の全部分圏の頂点条件。 -/
def KanRelativeJoinColimitVertex {K C : SSet.{u}} (p : K ⟶ C) (D : SSet.{u})
    (x : ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C))).obj D) _⦋0⦌) : Prop :=
  ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone p c
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C)) D).symm x))

/-- 概要：全ての fiber で普遍な相対 join 図式が張る全部分単体集合。
方針：関手単体集合の頂点条件で全部分複体を作る。
規約：余極限の存在を定義に仮定しない。
使われ方：普遍図式の ∞ 圏としての制限の始域。 -/
def kanRelativeJoinColimitDiagrams {K C : SSet.{u}} (p : K ⟶ C) (D : SSet.{u}) :
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C))).obj D).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (KanRelativeJoinColimitVertex p D)

/-- 概要：普遍な相対 join 図式を左端の元の図式へ制限する。
方針：全部分複体の包含の後に通常の関手の制限を合成する。
規約：元の射 p は任意。
使われ方：局所余極限から得る図式の coherent な選択の射。 -/
def kanRelativeJoinColimitRestriction {K C : SSet.{u}} (p : K ⟶ C) (D : SSet.{u}) :
    (kanRelativeJoinColimitDiagrams p D : SSet.{u}) ⟶ (ihom K).obj D :=
  (kanRelativeJoinColimitDiagrams p D).ι ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C))).app D

/-- 概要：普遍な相対 join 図式の制限は inner fibration。
方針：全部分複体の包含と単射による通常の関手の制限の内ホーン充填を合成する。
規約：D の quasicategory 性のみを要求する。
使われ方：写像空間の充満忠実性と頂点の全射性から全境界充填へ進む。 -/
instance kanRelativeJoinColimitRestriction_innerFibration {K C D : SSet.{u}}
    [Quasicategory D] (p : K ⟶ C) : InnerFibration (kanRelativeJoinColimitRestriction p D) := by
  have : InnerFibration (kanRelativeJoinColimitDiagrams p D).ι :=
    inferInstanceAs (InnerFibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (KanRelativeJoinColimitVertex p D)).ι)
  exact ⟨innerFibrations.comp_mem _ _ (InnerFibration.mem (q :=
    (kanRelativeJoinColimitDiagrams p D).ι))
      (InnerFibration.mem (q := (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C))).app D))⟩

/-- 概要：普遍な相対 join 図式の制限は写像空間の意味で充満忠実。
方針：各始点の局所余極限から制限の写像空間の同値を得て、全部分圏の包含の同値と合成する。
規約：相手の図式も含め、余極限の存在を追加仮定しない。
使われ方：Kan 図式の ∞ 圏としての普遍性。 -/
lemma kanRelativeJoinColimitRestriction_isFullyFaithful {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (kanRelativeJoinColimitRestriction p D) := by
  intro x y
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x
  change KanRelativeJoinColimitVertex p D x.val at hx
  let H := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C)) D).symm x.val
  have hH : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H = x.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ D).apply_symm_apply _
  have hinit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C))).app D) x.val := by
    rw [← hH]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFunctor_initialBoundary_of_colimit_fibers p H hx
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap
    ((kanRelativeJoinColimitDiagrams p D).ι ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C))).app D) x y)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp]
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _ x y).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pinchedHomMap_equivalence_of_initialBoundary _ x.val y.val hinit)

/-- 概要：各元の図式に必要な局所余極限があれば普遍図式の制限は頂点で全射。
方針：局所余極限から実際の相対 join 図式を構成して全部分圏へ含める。
規約：全ての元の図式 F の各 fiber の余極限を要求する。
使われ方：普遍な Kan 図式全体からの射の零次元の境界充填。 -/
lemma kanRelativeJoinColimitRestriction_surjective {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (hcol : ∀ (F : K ⟶ D) (c : C _⦋0⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c ≫ F)) :
    Function.Surjective ((kanRelativeJoinColimitRestriction p D).app (Opposite.op ⦋0⦌)) := by
  intro y
  obtain ⟨F, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K D).surjective y
  obtain ⟨H, hH, hHi⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanGlobalColimit_diagram_with_colimit_fibers p F (hcol F)
  have hv : KanRelativeJoinColimitVertex p D (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) := by
    intro c
    have hHv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C)) D).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) = H :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ D).symm_apply_apply H
    rw [hHv]
    exact hHi c
  let x : (kanRelativeJoinColimitDiagrams p D : SSet.{u}) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H, by
    intro α
    have hα : α = 𝟙 _ := Subsingleton.elim _ _
    simpa only [hα, op_id, Functor.map_id_apply] using hv⟩
  refine ⟨x, ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C) ≫ H) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F
  rw [hH]

/-- 概要：各元の図式に必要な局所余極限があれば普遍図式の制限は自明 Kan fibration。
方針：写像空間の充満忠実性、内ホーン充填、頂点の全射性を全境界充填へ合わせる。
規約：単なる本質的全射性でなく厳密な図式の延長から頂点を持ち上げる。
使われ方：普遍図式の coherent な選択とその可縮な一意性。 -/
lemma kanRelativeJoinColimitRestriction_trivialKanFibration {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (hcol : ∀ (F : K ⟶ D) (c : C _⦋0⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c ≫ F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (kanRelativeJoinColimitRestriction p D) := by
  have : Quasicategory (kanRelativeJoinColimitDiagrams p D : SSet.{u}) :=
    inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (KanRelativeJoinColimitVertex p D)))
  exact (kanRelativeJoinColimitRestriction_isFullyFaithful p).trivialKanFibration_of_surjective
    (kanRelativeJoinColimitRestriction_surjective p hcol)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
