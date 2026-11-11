module
public import SerrePositivity.KST.SConstruction.ZeroSpanChoices
public import SerrePositivity.KST.SConstruction.CofiberCompletion

/-! # 零射も固定した相対 cofiber 補完
概要：span 全体を指定した上で、既存境界を保つ cofiber 正方形の族を補完する。
方針：零脚の span の余極限の存在を、普遍押し出しの相対補完へ適用する。
規約：零頂点・零射を取り直さない。使われ方：BGT Lemma 7.3 の高次数の cofiber 補完。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：cofiber 正方形から span 全体を取る。
方針：全部分複体への包含後に始点側の二辺で制限する。
規約：零脚も指定に含む。使われ方：固定零射の相対補完の入力射影。 -/
def cofiberSpan (C : SSet.{u}) : cofiberDiagrams C ⟶ (ihom (horn 2 0 : SSet.{u})).obj C :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C

/-- 概要：正方形の span の零脚の終点は元の正方形の零角。
方針：第二辺の包含の式と関手頂点の評価を使う。
規約：C は任意。使われ方：指定 span の零条件を cofiber 条件へ戻す。 -/
lemma isZeroTargetArrow_pushoutSpan_iff {C : SSet.{u}}
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F)) ↔
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 1) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((horn₂₀.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ F).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ↔ _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
  rfl

/-- 概要：零脚つき span の族の全評価には余極限が存在する。
方針：各関手頂点を実際の span に戻し、固定零射の余極限存在を適用する。
規約：パラメーター B は任意、C は安定な quasicategory。
使われ方：普遍押し出しの相対補完の存在条件。 -/
lemma zeroSpanFamily_hasColimits {B C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (d : B ⟶ (ihom (horn 2 0 : SSet.{u})).obj C)
    (hd : ∀ v : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow
      (((pre horn₂₀.ι₀₂).app C).app (Opposite.op ⦋0⦌) (d.app (Opposite.op ⦋0⦌) v)))
    (v : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (horn 2 0 : SSet.{u}) C).symm
      (d.app (Opposite.op ⦋0⦌) v)) := by
  let p := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (horn 2 0 : SSet.{u}) C).symm (d.app (Opposite.op ⦋0⦌) v)
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p = d.app (Opposite.op ⦋0⦌) v :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _
  apply hasColimit_zeroSpan p
  have hz := hd v
  rw [← hp] at hz
  exact hz

/-- 概要：指定した零脚つき span を変えず、cofiber の族を任意の単射に沿い相対補完できる。
方針：各入力の余極限存在から押し出しの族を補完し、指定零脚の終点を用いて cofiber 部分複体へ持ち上げる。
規約：C は安定な quasicategory、既存の境界も span 全体も厳密に保つ。
使われ方：多段の cofiber 正方形を固定した零射の上で貼り合わせる。 -/
lemma exists_relative_cofiberFamily_over_span {A B C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (i : A ⟶ B) [Mono i] (d : B ⟶ (ihom (horn 2 0 : SSet.{u})).obj C)
    (hd : ∀ v : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow
      (((pre horn₂₀.ι₀₂).app C).app (Opposite.op ⦋0⦌) (d.app (Opposite.op ⦋0⦌) v)))
    (a : A ⟶ cofiberDiagrams C) (ha : a ≫ cofiberSpan C = i ≫ d) :
    ∃ F : B ⟶ cofiberDiagrams C, i ≫ F = a ∧ F ≫ cofiberSpan C = d := by
  obtain ⟨P, hP, hPd⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_relative_pushoutFamily i d (a ≫ cofiberForgetZero C) (by
    change (a ≫ cofiberForgetZero C ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsPushoutDiagramVertex).ι) ≫
      (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C = _
    rw [cofiberForgetZero_ι]
    exact ha) (zeroSpanFamily_hasColimits d hd)
  let g := P ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsPushoutDiagramVertex).ι
  have hgd : g ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C = d := hPd
  have hv (v : B _⦋0⦌) : IsCofiberDiagramVertex (g.app (Opposite.op ⦋0⦌) v) := by
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app hgd (Opposite.op ⦋0⦌)) v
    let W := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (g.app (Opposite.op ⦋0⦌) v)
    have hW : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex W = g.app (Opposite.op ⦋0⦌) v :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _
    have hz := hd v
    change ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C).app (Opposite.op ⦋0⦌)
      (g.app (Opposite.op ⦋0⦌) v) = d.app (Opposite.op ⦋0⦌) v at he
    rw [← hW] at he
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan W) = d.app (Opposite.op ⦋0⦌) v at he
    rw [← he] at hz
    refine ⟨(isZeroTargetArrow_pushoutSpan_iff W).1 hz, ?_⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (P.app (Opposite.op ⦋0⦌) v)
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift IsCofiberDiagramVertex g hv
  have hF : F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι = g :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  refine ⟨F, ?_, ?_⟩
  · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι).1
    rw [Category.assoc, hF]
    dsimp only [g]
    rw [← Category.assoc, hP, Category.assoc, cofiberForgetZero_ι]
  · change (F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι) ≫
      (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C = d
    rw [hF]
    exact hgd

/-- 概要：零脚つき span の族の上では cofiber の span 射影の引き戻しは trivial Kan fibration。
方針：各境界の持ち上げを、span 全体を固定する相対 cofiber 補完で構成する。
規約：パラメーター B は任意。使われ方：固定した零射上の全選択の可縮性。 -/
lemma cofiberSpan_pullback_trivialKanFibration {B C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (d : B ⟶ (ihom (horn 2 0 : SSet.{u})).obj C)
    (hd : ∀ v : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow
      (((pre horn₂₀.ι₀₂).app C).app (Opposite.op ⦋0⦌) (d.app (Opposite.op ⦋0⦌) v))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullback.snd (cofiberSpan C) d) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  have ha : (a ≫ pullback.fst (cofiberSpan C) d) ≫ cofiberSpan C =
      (boundary n).ι ≫ (b ≫ d) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, sq.w, Category.assoc]
  obtain ⟨F, hF, hFd⟩ := exists_relative_cofiberFamily_over_span (boundary n).ι (b ≫ d)
    (fun v => hd (b.app (Opposite.op ⦋0⦌) v)) (a ≫ pullback.fst _ _) ha
  refine CommSq.HasLift.mk' {
    l := pullback.lift F b hFd
    fac_left := ?_
    fac_right := pullback.lift_snd _ _ _ }
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    exact hF
  · rw [Category.assoc, pullback.lift_snd]
    exact sq.w.symm

/-- 概要：指定した零脚つき span の cofiber 正方形の全選択空間は可縮 Kan 複体。
方針：入力を定値にした相対補完で全ての境界を充填する。
規約：空間は実際の span 射影の vertex fiber。使われ方：零射を固定した選択の一意性。 -/
lemma cofiberSpan_vertexFiber_isContractibleKan {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (p : (horn 2 0 : SSet.{u}) ⟶ C)
    (hp : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₂ ≫ p))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (cofiberSpan C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) := by
  intro n a
  have ha : (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (cofiberSpan C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) ≫ cofiberSpan C =
      (boundary n).ι ≫ (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) : (Δ[n] : SSet.{u}) ⟶ _) := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
  obtain ⟨F, hF, hFd⟩ := exists_relative_cofiberFamily_over_span (boundary n).ι
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) (fun v => by
      change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow (((pre horn₂₀.ι₀₂).app C).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) 0))
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
      exact hp) (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (cofiberSpan C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) ha
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (cofiberSpan C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) F hFd, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
  exact hF

end SerrePositivity.KST.SConstruction
