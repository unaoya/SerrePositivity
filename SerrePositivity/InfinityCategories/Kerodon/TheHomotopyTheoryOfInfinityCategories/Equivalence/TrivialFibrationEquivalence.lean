module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：trivial Kan fibration から明示的な quasicategory の同値を構成する。
方針：切断を選び、内部 Hom の可縮な fiber で単位の可逆二胞体を作る。
規約：モデル構造や弱同値は用いない。
使われ方：Kerodon Proposition 4.5.4.11（Tag 01EG）、Theorem 4.8.4.1（Tag 01JX）。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：内部 Hom による後合成は trivial Kan fibration 性を保つ。
方針：閉構造の随伴で境界の持ち上げを積の境界の持ち上げへ移す。
規約：パラメーター A は任意。
使われ方：Kerodon Proposition 4.5.4.11（Tag 01EG） の切断の空間。 -/
instance trivialKanFibration_ihom_map {E B : SSet.{u}} (p : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (A : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((ihom A).map p) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  let sq := Functor.PushoutObjObj.ofIsInitialLeft (curriedTensor SSet.{u})
    (initial.to A) (boundary n).ι initialIsInitial
  let sq' := Functor.PullbackObjObj.ofIsInitial internalHom (initial.to A) p initialIsInitial
  change HasLiftingProperty (boundary n).ι sq'.π
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
  change HasLiftingProperty (A ◁ (boundary n).ι) p
  have hm : Mono (A ◁ (boundary n).ι) := by
    rw [NatTrans.mono_iff_mono_app]
    intro d
    rw [mono_iff_injective]
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    change (a, b.val) = (a', b'.val) at h
    exact Prod.ext
      (congrArg (fun z : A.obj d × (Δ[n] : SSet.{u}).obj d ↦ z.1) h)
      (Subtype.ext (congrArg (fun z : A.obj d × (Δ[n] : SSet.{u}).obj d ↦ z.2) h))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) _ hm

/-- 概要：trivial Kan fibration には厳密な切断が存在する。
方針：空部分複体から標的への単射に対して持ち上げる。
規約：切断との合成は標的の恒等射。
使われ方：Kerodon Proposition 4.5.4.11（Tag 01EG） の同値の逆射。 -/
lemma trivialKanFibration_exists_section {E B : SSet.{u}} (p : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] : ∃ s : B ⟶ E, s ≫ p = 𝟙 B := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) (⊥ : B.Subcomplex).ι inferInstance
  have sq : CommSq (Subcomplex.isInitialBot.to E) (⊥ : B.Subcomplex).ι p (𝟙 B) :=
    ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_right⟩

/-- 概要：quasicategory 間の trivial Kan fibration は A3a の明示的な同値。
方針：切断を逆射とし、内部 Hom の可縮な fiber で単位の可逆二胞体を作る。
規約：順方向の射は与えられた p そのもの。
使われ方：Kerodon Proposition 4.5.4.11（Tag 01EG）、Theorem 4.8.4.1（Tag 01JX）。 -/
@[kerodon 01EH]
noncomputable def qCatEquivalenceOfTrivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence E B := by
  let s := Classical.choose (trivialKanFibration_exists_section p)
  have hs : s ≫ p = 𝟙 B := Classical.choose_spec (trivialKanFibration_exists_section p)
  let q := (ihom E).map p
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan q b
  have := hc.kanComplex
  let v₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (p ≫ s), by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((p ≫ s) ≫ p) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p
    rw [Category.assoc, hs, Category.comp_id]⟩
  let v₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 E), by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((𝟙 E) ≫ p) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p
    rw [Category.id_comp]⟩
  let hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso (hc.isTerminalVertex v₀) (hc.isTerminalVertex v₁)
  refine { hom := p
           inv := s
           homInvIso := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map hi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b)
           invHomIso := ?_ }
  exact eqToIso (congrArg (fun f : B ⟶ B ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) hs)

/-- 概要：quasicategory 間の trivial Kan fibration は同値という性質を持つ。
方針：明示的な同値のデータを存在量化する。
規約：射 p を固定した同値性。
使われ方：Kerodon Theorem 4.8.4.1（Tag 01JX） のファイブレーションへの還元。 -/
@[kerodon 01EH, kerodon 04FA]
lemma isQCatEquivalence_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence p := (qCatEquivalenceOfTrivialKanFibration p).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.4.4.6" (partial := stronger-hyp) "仮定：準圏間の Cartesian p にさらに EquivalenceLifting p を追加（Lean が強い）。結論：native QCatEquivalence⇒TrivialKanFibration と逆方向の二宣言で、同じ p の iff を得る。Cartesian 性から EquivalenceLifting を導く型はここでは得ていない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
attribute [cite HTT "4.3.1.2" (partial := component) "仮定：内ファイブレーションと右結合上の余錐（Lean が強い：圏同値の判定では始域と終域が準圏）。結論：同じ相対コスライス比較の自明 Kan 性と準圏同値性が同値（Joyal 模型でのホモトピー引き戻しの同定は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
attribute [cite HTT "4.3.2.16" (partial := stronger-hyp) "仮定：部分圏上の全関手に相対左 Kan 拡張が存在（Lean が強い：固定した底図式だけでなく、両立する任意の部分図式と底図式に対する局所相対余極限を要求）。結論：同じ相対制限の自明 Kan 性から切断を得る。切断の値は相対左 Kan 関手の充満部分圏にあり、同じ制限の繊維が可縮なのでその部分圏の全関手を本質像に含む（一致する場合）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section
attribute [cite HTT "5.4.5.1" (partial := special) "仮定：accessible な C と終対象 x の一点図式（Lean が強い：任意の小図式 p ではなく終対象の一点）。結論：元の C/x は C への同じ射影が trivial Kan fibration、従って全準圏同値となるので accessible（この場合に一致）。同値模型を新しく仮定するのでなく終対象の既存判定から構成する。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration
attribute [cite HTT "5.4.5.15" (partial := special) "仮定：τ-accessible な C と τ-compact な始対象 x の一点図式（Lean が強い：一般の κ-small compact 図式を始対象の一点に限定）。結論：同じ Cx/ は C への射影が全準圏同値なので τ-accessible、かつ元の余錐の τ-compact 性は射影頂点の τ-compact 性と同値（この場合に両結論が一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration
attribute [cite HTT "5.4.5.16" (partial := special) "仮定：accessible な C と始対象 x の一点図式（Lean が強い）。結論：元の Cx/ の射影は終始対象の境界判定から trivial Kan fibration であり、C と全同値なので accessible（この場合に一致）。一般の小図式の下圏の生成性を結論したとは数えない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration
attribute [cite HTT "5.4.6.7" (partial := special) "仮定：accessible な C と終対象 x の一点図式（Lean が強い：p を終対象の一点に限定）。結論：同じ C/x は実際の射影によって C と全準圏同値、従って accessible（この場合に一致）。元の全 Hom と高次単体を保つ同値であり、通常圏の上圏への置換ではない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration
attribute [cite HTT "5.5.3.10" (partial := special) "仮定：presentable C と終対象 x の一点図式（Lean が強い：一般の小図式 p を終対象の一点に限定）。結論：同じ C/x の元の射影が全準圏同値であるため C/x は presentable（この場合に一致）。元の射影の同値は終対象の境界条件から構成でき、別の圏との未供給比較ではない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration
attribute [cite HTT "5.5.3.11" (partial := special) "仮定：presentable C と始対象 x の一点図式（Lean が強い：p を始対象の一点に限定）。結論：同じ Cx/ の元の射影が全準圏同値なので Cx/ は presentable（この場合に一致）。一般の小図式の下圏の compact 生成性は結論しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration
