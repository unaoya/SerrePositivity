module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathIso

/-!
概要：関手の可逆 path による置換。
方針：可逆 path の始点評価を与えられた関手で引き戻す。
規約：始域への射影は trivial Kan fibration、終点評価を置換された関手とする。
使われ方：Kerodon §4.5.3（Tag 032Y）、Theorem 4.8.4.1（Tag 01JX） の同値判定への還元。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：trivial Kan fibration の引き戻しの射影も trivial Kan fibration。
方針：単射の rlp が基底変換で閉じることを使う。
規約：任意の単体集合に沿う引き戻し。
使われ方：Kerodon §4.5.3（Tag 032Y） の path による置換。 -/
instance trivialKanFibration_pullback_snd {E B A : SSet.{u}} (p : E ⟶ B) (f : A ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullback.snd p f) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.pullback_snd p f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p))⟩

/-- 概要：関手の可逆 path による置換の単体集合。
方針：path の始点と関手の像を引き戻しで一致させる。
規約：終点は自由に動かす。
使われ方：Kerodon §4.5.3（Tag 032Y）、Theorem 4.8.4.1（Tag 01JX）。 -/
noncomputable def equivalencePathReplacement {X Y : SSet.{u}} (f : X ⟶ Y) : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) f

/-- 概要：path による置換から元の始域への射影。
方針：引き戻しの第二射影を取る。
規約：元の頂点を記憶する射。
使われ方：Kerodon §4.5.3（Tag 032Y） の同値である射影。 -/
noncomputable def equivalencePathReplacementProjection {X Y : SSet.{u}} (f : X ⟶ Y) :
    equivalencePathReplacement f ⟶ X := pullback.snd _ _

/-- 概要：path による置換の始域への射影は trivial Kan fibration。
方針：始点評価の持ち上げ性を引き戻す。
規約：標的 Y が quasicategory。
使われ方：Kerodon §4.5.3（Tag 032Y） の置換の同値性。 -/
instance equivalencePathReplacementProjection_trivialKanFibration {X Y : SSet.{u}}
    [Quasicategory Y] (f : X ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (equivalencePathReplacementProjection f) :=
  trivialKanFibration_pullback_snd _ _

/-- 概要：quasicategory 間の関手の path による置換も quasicategory。
方針：始域への射影の inner fibration 性を使う。
規約：両端の quasicategory 性を仮定する。
使われ方：Kerodon §4.5.3（Tag 032Y）、Theorem 4.8.4.1（Tag 01JX）。 -/
instance equivalencePathReplacement_quasicategory {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) :
    Quasicategory (equivalencePathReplacement f) :=
  quasicategory_of_innerFibration (equivalencePathReplacementProjection f)

/-- 概要：path による置換の終点を取る関手。
方針：引き戻しの第一射影を終点で評価する。
規約：元の関手との一致は可逆 path による。
使われ方：Kerodon §4.5.3（Tag 032Y） の置換された関手。 -/
noncomputable def equivalencePathReplacementMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    equivalencePathReplacement f ⟶ Y :=
  pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 1

/-- 概要：path の置換の射影後の元の関手と終点評価は関手単体集合で同型。
方針：引き戻しに付随する可逆 path のホモトピーを比較する。
規約：始域の quasicategory 性は不要。
使われ方：Kerodon §4.5.3（Tag 032Y）、Theorem 4.8.4.1（Tag 01JX） の関手の比較。 -/
noncomputable def equivalencePathReplacementFunctorIso {X Y : SSet.{u}}
    [Quasicategory Y] (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (equivalencePathReplacementProjection f ≫ f) (equivalencePathReplacementMap f) := by
  let a := pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) f
  let H := uncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y)
  have hC : curry H = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y := curry_uncurry _
  have hv : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))) := by
    intro x
    have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) x)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex ((a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y).app (Opposite.op ⦋0⦌) x) at hx
    rw [← hC] at hx
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex at hx
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_curry] at hx
    exact hx
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (equivalencePathReplacement f) ≫ H =
      equivalencePathReplacementProjection f ≫ f := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hC]
    exact pullback.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) (g := f)
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (equivalencePathReplacement f) ≫ H =
      equivalencePathReplacementMap f := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hC]
    rfl
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfEquivalenceHomotopy H hv
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (equivalencePathReplacement f) ≫ H)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (equivalencePathReplacement f) ≫ H) at e
  rw [h₀, h₁] at e
  exact e

/-- 概要：元の始域を定値 path として置換へ送る射。
方針：定値 path と恒等射を引き戻しに持ち上げる。
規約：元の関手との合成は厳密に一致する。
使われ方：Kerodon §4.5.3（Tag 032Y） の置換の切断。 -/
noncomputable def equivalencePathReplacementSection {X Y : SSet.{u}} (f : X ⟶ Y) :
    X ⟶ equivalencePathReplacement f :=
  pullback.lift (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl Y) (𝟙 X) (by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl_endpoint, Category.comp_id, Category.id_comp])

/-- 概要：定値 path の切断と始域への射影の合成は恒等射。
方針：引き戻しの第二成分を取る。
規約：厳密な等式。
使われ方：Kerodon §4.5.3（Tag 032Y） の置換の同値性。 -/
lemma equivalencePathReplacementSection_projection {X Y : SSet.{u}} (f : X ⟶ Y) :
    equivalencePathReplacementSection f ≫ equivalencePathReplacementProjection f = 𝟙 X :=
  pullback.lift_snd _ _ _

/-- 概要：定値 path の切断と置換された関手の合成は元の関手。
方針：引き戻しの第一成分を終点で評価する。
規約：厳密な等式。
使われ方：Kerodon §4.5.3（Tag 032Y） の関手の分解。 -/
lemma equivalencePathReplacementSection_map {X Y : SSet.{u}} (f : X ⟶ Y) :
    equivalencePathReplacementSection f ≫ equivalencePathReplacementMap f = f := by
  change equivalencePathReplacementSection f ≫
    pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 1 = f
  unfold equivalencePathReplacementSection
  rw [← Category.assoc, pullback.lift_fst, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl_endpoint, Category.comp_id]

/-- 概要：元の関手が同値であることと path で置換した関手が同値であることは同値。
方針：始域への射影の同値と可逆な関手の比較に二対三則を適用する。
規約：両端の quasicategory 性を仮定する。
使われ方：Kerodon Theorem 4.8.4.1（Tag 01JX） の置換への還元。 -/
lemma isQCatEquivalence_iff_equivalencePathReplacementMap {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (equivalencePathReplacementMap f) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (equivalencePathReplacementProjection f)
  have e := equivalencePathReplacementFunctorIso f
  constructor
  · intro hf
    exact (hp.comp hf).ofFunctorIso e
  · intro hq
    exact hp.cancel_left (hq.ofFunctorIso e.symm)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
