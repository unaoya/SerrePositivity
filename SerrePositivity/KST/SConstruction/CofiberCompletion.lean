module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PushoutCompletion
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SuspensionDiagramArrows
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition

/-! # 射の族に対する cofiber 補完
概要：零角を持つ押し出し四角形を、入力の射へ制限する。
方針：零対象へ向かう辺と普遍的な押し出しを順に補完する。
規約：零対象の選択を固定しない。使われ方：∞-S• の相対 cofiber 構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 概要：関手の四角形が零角を持つ押し出しである条件。
方針：零角と α-S の押し出し性を組にする。
規約：零角は (0,1)。使われ方：cofiber 図式の全部分圏。 -/
def IsCofiberDiagramVertex {C : SSet.{u}}
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v) 0 1) ∧ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsPushoutDiagramVertex v

/-- 概要：cofiber 四角形全体の単体集合。
方針：実際の四角形の関手単体集合の全部分複体を取る。
規約：高次の自然性を保持する。使われ方：cofiber をパラメーター付きで選ぶ。 -/
def cofiberDiagrams (C : SSet.{u}) : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C)
    IsCofiberDiagramVertex : SSet.{u})

/-- 概要：cofiber 四角形の入力となる射を取る。
方針：正方形の下辺に制限する。
規約：入力の始点は (0,0)、終点は (1,0)。使われ方：相対 cofiber 補完の基底。 -/
def cofiberProjection (C : SSet.{u}) : cofiberDiagrams C ⟶ (ihom (Δ[1] : SSet.{u})).obj C :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app C

/-- 概要：cofiber 四角形の零角の条件を忘れて押し出し四角形にする。
方針：同じ関手頂点の押し出し条件を使う。
規約：四角形自体は変えない。使われ方：押し出しの境界充填への比較。 -/
def cofiberForgetZero (C : SSet.{u}) : cofiberDiagrams C ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutDiagrams C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι
    (fun v ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v).2)

/-- 概要：零角の条件を忘れた四角形の包含は元の包含。
方針：全部分複体の持ち上げの式。
規約：厳密等号。使われ方：族の境界の照合。 -/
lemma cofiberForgetZero_ι (C : SSet.{u}) :
    cofiberForgetZero C ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsPushoutDiagramVertex).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι := rfl

/-- 概要：cofiber 四角形の左辺は零対象へ向かう辺。
方針：零角の頂点条件を左辺の終点評価へ移す。
規約：始点は入力の射と共有する。使われ方：零対象へ向かう辺の相対選択。 -/
def cofiberZeroArrow (C : SSet.{u}) : cofiberDiagrams C ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrows C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫
    (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge).app C) (by
      intro v
      have hz := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v).1
      have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val) = v.val :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply v.val
      change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow (((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge).app C).app (Opposite.op ⦋0⦌) v.val)
      rw [← hv]
      change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val))
      unfold _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
      exact hz)

/-- 概要：零対象への左辺を含めると通常の左辺への制限。
方針：全部分複体の持ち上げの式。
規約：厳密等号。使われ方：補完の境界の照合。 -/
lemma cofiberZeroArrow_ι (C : SSet.{u}) :
    cofiberZeroArrow C ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge).app C := rfl

/-- 概要：左の零対象への辺と入力の射は始点を共有する。
方針：前合成と評価の交換を使い、二辺の始点を比較する。
規約：高次単体でも厳密に一致する。使われ方：span の族の貼り合わせ。 -/
lemma cofiberZeroArrow_source (C : SSet.{u}) :
    cofiberZeroArrow C ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource C =
      cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge).app C) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app C) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  rfl

/-- 概要：押し出しの入力 span の第一辺は正方形の下辺。
方針：span の包含と前合成の合成則を使う。
規約：0→1 の辺。使われ方：補完した四角形の入力の回収。 -/
lemma pushoutProjection_bottom (C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutProjection C ≫ (pre horn₂₀.ι₀₁).app C =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsPushoutDiagramVertex).ι ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app C := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutProjection, Category.assoc, ← NatTrans.comp_app, ← pre_map,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge]

end SerrePositivity.KST.SConstruction
