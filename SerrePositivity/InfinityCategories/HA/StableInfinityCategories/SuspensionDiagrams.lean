module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FullSubcomplexIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SuspensionDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Pointed
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare

/-! # Suspension と loop の図式の族

概要：二つの零角を持つ普遍四角形を、正方形からの関手 ∞ 圏の全部分圏に束ねる。
方針：頂点条件で普遍性を課し、左右の対角の評価を単体的な射として使う。
規約：評価の同値性はここではまだ主張しない。使われ方：S3 の h C 上の関手の構成。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial

/-- 概要：四角形の頂点表示を戻すと元の四角形。
方針：関手頂点の同値の両逆性を使う。
規約：厳密な等式。使われ方：選んだ四角形を族の頂点にする。 -/
lemma squareDiagram_functorVertex {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) = F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply F

/-- 概要：loop 図式の頂点条件は二つの零角と引き戻し性。
方針：図式の実際の四角形に条件を課す。
規約：対角の頂点は自由に動く。使われ方：loop 図式の全部分圏。 -/
def IsLoopDiagramVertex {X : SSet.{u}}
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v) 0 1) ∧
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v) 1 0) ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v)

/-- 概要：全 loop 図式からなる関手 ∞ 圏の全部分単体集合。
方針：各頂点で零角と引き戻し性を課す。
規約：高次単体は実際の四角形の族。使われ方：loop の関手性。 -/
def loopDiagrams (X : SSet.{u}) : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
    IsLoopDiagramVertex : SSet.{u})

/-- 概要：suspension 図式の族は quasicategory をなす。
方針：関手 ∞ 圏の全部分圏のホーン充填を使う。
規約：C の安定性は不要。使われ方：図式の族のホモトピー圏。 -/
instance suspensionDiagrams_quasicategory (X : SSet.{u}) [Quasicategory X] :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagrams X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

/-- 概要：loop 図式の族は quasicategory をなす。
方針：関手 ∞ 圏の全部分圏のホーン充填を使う。
規約：C の安定性は不要。使われ方：図式の族のホモトピー圏。 -/
instance loopDiagrams_quasicategory (X : SSet.{u}) [Quasicategory X] :
    Quasicategory (loopDiagrams X) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

/-- 概要：loop 図式を指定した角で評価する単体的な射。
方針：全部分圏の包含と関手の評価を合成する。
規約：全ての高次単体に自然。使われ方：Ω の始点・終点の関手。 -/
def loopDiagramEvaluation (X : SSet.{u}) (i j : Fin 2) : loopDiagrams X ⟶ X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)

/-- 概要：安定 ∞ 圏の四角形は suspension 図式であることと loop 図式であることが同値。
方針：零角を保ち、安定性の fiber/cofiber 判定を適用する。
規約：図式全体を同じ四角形のまま保つ。使われ方：ΣΩ の図式の族の比較。 -/
lemma isSuspensionDiagramVertex_iff_isLoopDiagramVertex {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsSuspensionDiagramVertex v ↔ IsLoopDiagramVertex v := by
  constructor
  · rintro ⟨hz, hw, hp⟩
    exact ⟨hz, hw, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout ⟨_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v, hz⟩ hp⟩
  · rintro ⟨hz, hw, hp⟩
    exact ⟨hz, hw, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback ⟨_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v, hz⟩ hp⟩

/-- 概要：安定 ∞ 圏の suspension 図式と loop 図式は単体集合として同型。
方針：同じ関手 ∞ 圏で頂点条件の同値を全部分圏に制限する。
規約：図式と高次の族を変えない。使われ方：ΣΩ の逆性の構成。 -/
def suspensionLoopDiagramsIso (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagrams X ≅ loopDiagrams X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexIso (Iso.refl _) _ _ (isSuspensionDiagramVertex_iff_isLoopDiagramVertex)

/-- 概要：図式の族の同型は全ての角の評価と可換。
方針：各次数で同じ四角形を評価する。
規約：厳密な可換性。使われ方：h C の ΣΩ の単位と余単位。 -/
lemma suspensionLoopDiagramsIso_evaluation (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (i j : Fin 2) :
    (suspensionLoopDiagramsIso X).hom ≫ loopDiagramEvaluation X i j =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X i j := rfl

/-- 概要：suspension 四角形は図式の族の頂点となる。
方針：零単体の全ての頂点制限は恒等なので、三つの条件をそのまま入れる。
規約：始点を指定した四角形を使う。使われ方：始点評価の全射性。 -/
def SuspensionSquare.diagramVertex {X : SSet.{u}} {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagrams X) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square, by
    intro v
    have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hv, op_id, CategoryTheory.Functor.map_id_apply]
    unfold _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsSuspensionDiagramVertex
    rw [squareDiagram_functorVertex]
    exact ⟨s.zero_corner, s.other_zero, s.isPushout⟩⟩

/-- 概要：loop 四角形は図式の族の頂点となる。
方針：零単体の全ての頂点制限は恒等なので、三つの条件をそのまま入れる。
規約：終点を指定した四角形を使う。使われ方：終点評価の全射性。 -/
def LoopSquare.diagramVertex {X : SSet.{u}} {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare x) :
    (loopDiagrams X) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square, by
    intro v
    have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hv, op_id, CategoryTheory.Functor.map_id_apply]
    unfold IsLoopDiagramVertex
    rw [squareDiagram_functorVertex]
    exact ⟨s.zero_corner, s.other_zero, s.isPullback⟩⟩

/-- 概要：suspension 四角形の族での評価は元の角の頂点。
方針：関手頂点を評価する公式を使う。
規約：任意の角。使われ方：族と対象ごとの構成の照合。 -/
lemma SuspensionSquare.diagramVertex_evaluation {X : SSet.{u}} {x : X _⦋0⦌}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) (i j : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X i j).app (Opposite.op ⦋0⦌) s.diagramVertex =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square i j :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex _ s.square

/-- 概要：loop 四角形の族での評価は元の角の頂点。
方針：関手頂点を評価する公式を使う。
規約：任意の角。使われ方：族と対象ごとの構成の照合。 -/
lemma LoopSquare.diagramVertex_evaluation {X : SSet.{u}} {x : X _⦋0⦌}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare x) (i j : Fin 2) :
    (loopDiagramEvaluation X i j).app (Opposite.op ⦋0⦌) s.diagramVertex =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square i j :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex _ s.square

/-- 概要：安定 ∞ 圏では suspension 図式の始点評価は頂点上全射。
方針：選んだ suspension 四角形を使う。
規約：射・高次単体上の全射性はまだ含めない。使われ方：Σ の構成の本質的全射性。 -/
lemma suspensionDiagramEvaluation_source_surjective (X : SSet.{u})
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0).app (Opposite.op ⦋0⦌)) := by
  intro x
  refine ⟨(_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenSuspensionSquare x).diagramVertex, ?_⟩
  exact ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenSuspensionSquare x).diagramVertex_evaluation 0 0).trans
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenSuspensionSquare x).source_eq

/-- 概要：安定 ∞ 圏では loop 図式の終点評価は頂点上全射。
方針：選んだ loop 四角形を使う。
規約：射・高次単体上の全射性はまだ含めない。使われ方：Ω の構成の本質的全射性。 -/
lemma loopDiagramEvaluation_target_surjective (X : SSet.{u})
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    Function.Surjective ((loopDiagramEvaluation X 1 1).app (Opposite.op ⦋0⦌)) := by
  intro x
  refine ⟨(_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenLoopSquare x).diagramVertex, ?_⟩
  exact ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenLoopSquare x).diagramVertex_evaluation 1 1).trans (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenLoopSquare x).target_eq

/-- 概要：suspension 図式の始点評価は本質的全射である。
方針：頂点上の厳密な全射性を h C の恒等同型で証明する。
規約：安定 ∞ 圏。使われ方：評価の同値性の本質的全射側。 -/
lemma suspensionDiagramEvaluation_source_essentiallySurjective (X : SSet.{u})
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0) := by
  intro x
  obtain ⟨s, hs⟩ := suspensionDiagramEvaluation_source_surjective X x
  exact ⟨s, ⟨eqToIso (congrArg SSet.HomotopyCategory.mk hs)⟩⟩

/-- 概要：loop 図式の終点評価は本質的全射である。
方針：頂点上の厳密な全射性を h C の恒等同型で証明する。
規約：安定 ∞ 圏。使われ方：評価の同値性の本質的全射側。 -/
lemma loopDiagramEvaluation_target_essentiallySurjective (X : SSet.{u})
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (loopDiagramEvaluation X 1 1) := by
  intro x
  obtain ⟨s, hs⟩ := loopDiagramEvaluation_target_surjective X x
  exact ⟨s, ⟨eqToIso (congrArg SSet.HomotopyCategory.mk hs)⟩⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
