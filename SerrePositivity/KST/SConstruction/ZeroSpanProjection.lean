module
public import SerrePositivity.KST.SConstruction.RelativeZeroSpanCompletion

/-! # cofiber の零脚つき span への射影
概要：零脚を持つ span の全部分複体を標的に取ると、cofiber の射影は trivial Kan fibration。
方針：span 全体を固定した相対補完を各境界に適用する。
規約：入力の零頂点・零射も動くが厳密に回収する。
使われ方：BGT Lemma 7.3 のパラメーター付き補完と枠の同時固定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：span の第二辺の終点が零対象である条件。
方針：第二辺への制限で判定する。
規約：全体の図式の関手頂点に課す。使われ方：零脚つき span の全部分複体。 -/
def IsZeroSpanVertex {C : SSet.{u}} (v : ((ihom (horn 2 0 : SSet.{u})).obj C) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow (((pre horn₂₀.ι₀₂).app C).app (Opposite.op ⦋0⦌) v)

/-- 概要：零脚つき span の全図式を保持する全部分単体集合。
方針：零終点の頂点条件による全部分複体。
規約：余極限の選択は含めない。使われ方：cofiber の固定 span 入力。 -/
def zeroSpanDiagrams (C : SSet.{u}) : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 0 : SSet.{u})).obj C) IsZeroSpanVertex : SSet.{u})

/-- 概要：零脚つき span の図式の全部分複体は quasicategory。
方針：関手 quasicategory の全部分複体であることを使う。
規約：C は quasicategory。使われ方：高次の図式の同型と普遍性の比較。 -/
instance zeroSpanDiagrams_quasicategory (C : SSet.{u}) [Quasicategory C] :
    Quasicategory (zeroSpanDiagrams C) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

/-- 概要：cofiber 正方形から零脚つき span への射影。
方針：通常の span 射影を零終点の全部分複体へ持ち上げる。
規約：零射も入力として厳密に保持する。使われ方：複数の cofiber の相対的な選択。 -/
def cofiberSpanProjection (C : SSet.{u}) : cofiberDiagrams C ⟶ zeroSpanDiagrams C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift IsZeroSpanVertex (cofiberSpan C) (by
    intro v
    let W := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val
    have hW : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex W = v.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow (((pre horn₂₀.ι₀₂).app C).app (Opposite.op ⦋0⦌)
      (((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C).app (Opposite.op ⦋0⦌) v.val))
    rw [← hW]
    exact (isZeroTargetArrow_pushoutSpan_iff W).2 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v).1)

/-- 概要：零脚の条件を忘れると通常の cofiber の span 射影。
方針：全部分複体の持ち上げの定義。
規約：全次数で厳密等号。使われ方：相対持ち上げ問題の比較。 -/
lemma cofiberSpanProjection_ι (C : SSet.{u}) :
    cofiberSpanProjection C ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroSpanVertex).ι = cofiberSpan C := rfl

/-- 概要：安定な quasicategory の cofiber の span 射影は trivial Kan fibration。
方針：任意の境界に対し、span 全体と既存境界を保つ補完を構成する。
規約：元の零頂点・零射の表示を変えない。
使われ方：内部 Hom と相対内部 Hom による高次数の同時補完。 -/
instance cofiberSpanProjection_trivialKanFibration (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (cofiberSpanProjection C) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  let ι : zeroSpanDiagrams C ⟶ (ihom (horn 2 0 : SSet.{u})).obj C :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroSpanVertex).ι
  have ha : a ≫ cofiberSpan C = (boundary n).ι ≫ (b ≫ ι) := by
    rw [← cofiberSpanProjection_ι, ← Category.assoc, sq.w, Category.assoc]
  obtain ⟨F, hF, hFb⟩ := exists_relative_cofiberFamily_over_span (boundary n).ι (b ≫ ι)
    (fun v => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (b.app (Opposite.op ⦋0⦌) v)) a ha
  refine CommSq.HasLift.mk' {
    l := F
    fac_left := hF
    fac_right := ?_ }
  apply (cancel_mono ι).1
  rw [Category.assoc]
  change F ≫ (cofiberSpanProjection C ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroSpanVertex).ι) = b ≫ ι
  rw [cofiberSpanProjection_ι]
  exact hFb

end SerrePositivity.KST.SConstruction
