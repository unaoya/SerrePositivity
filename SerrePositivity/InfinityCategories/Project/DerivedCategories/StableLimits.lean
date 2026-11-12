module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PullbackPresentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.AcyclicVertex
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiniteShapes

/-! # 導来 ∞ 圏の零対象と fiber の存在

概要：D(S) は実際の零頂点を持ち、任意の cospan の極限と任意の辺の fiber を持つ。
方針：N7 の標準 semifree fiber 四角形を任意の cospan の上へ置き、S1 の構成を適用する。
規約：IsStable はまだ仮定も結論にも使わない。使われ方：D7 の安定性の零・fiber 側。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial ZeroObject

variable (S : Type u) [CommRing S]

/-- 概要：D(S) の零複体の頂点は ∞ 圏の零対象。
方針：N7 の同じ頂点の始対象性・終対象性を組み合わせる。
規約：h の零性ではなく境界充填による零性。使われ方：pointed 条件。 -/
lemma derivedInfinityZeroVertex_isZeroVertex : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityZeroVertex S) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isInitialVertex_semifree_zero S, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isTerminalVertex_semifree_zero S⟩

/-- 概要：D(S) は零頂点を持つ。
方針：semifree な零複体を選ぶ。
規約：選択を伴わない存在条件。使われ方：fiber/cofiber の存在の入力。 -/
instance derivedInfinityCategory_hasZeroVertex : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) where
  exists_zero := ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityZeroVertex S, derivedInfinityZeroVertex_isZeroVertex S⟩

variable {S}

/-- 概要：任意の D(S) の cospan の三複体と鎖写像の表示。
方針：全複体の dg nerve へ含めて標準表示を取る。
規約：四角形への延長を仮定しない。使われ方：全ての cospan の極限の存在。 -/
abbrev derivedCospanPresentation
    (p : (horn 2 2 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComplexCospanPresentation (p ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.presentComplexCospan (p ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)

/-- 概要：抽出した cospan の左複体は semifree。
方針：左の一単体の始頂点の所属を読む。
規約：極限性は不要。使われ方：標準 fiber 四角形の構成。 -/
lemma derivedCospanPresentation_left
    (p : (horn 2 2 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (derivedCospanPresentation p).leftObj := by
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) 1 := SSet.yonedaEquiv (horn₂₂.ι₀₂ ≫ p)
  exact (s.obj 0).property

/-- 概要：抽出した cospan の右複体は semifree。
方針：右の一単体の始頂点の所属を読む。
規約：任意の cospan。使われ方：標準 fiber 四角形の構成。 -/
lemma derivedCospanPresentation_right
    (p : (horn 2 2 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (derivedCospanPresentation p).rightObj := by
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) 1 := SSet.yonedaEquiv (horn₂₂.ι₁₂ ≫ p)
  exact (s.obj 0).property

/-- 概要：抽出した cospan の終域は semifree。
方針：左の一単体の終頂点の所属を読む。
規約：任意の cospan。使われ方：標準 fiber 四角形の構成。 -/
lemma derivedCospanPresentation_target
    (p : (horn 2 2 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (derivedCospanPresentation p).targetObj := by
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) 1 := SSet.yonedaEquiv (horn₂₂.ι₀₂ ≫ p)
  exact (s.obj 1).property

/-- 概要：任意の cospan の標準 fiber 四角形を D(S) 内で作る。
方針：semifree の有限直和・fiber 閉性を N7 の四角形へ適用する。
規約：cospan の二辺の表示をそのまま使う。使われ方：極限錐の選択。 -/
def derivedCospanFiberSquare
    (p : (horn 2 2 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFiberSquare (derivedCospanPresentation p).leftMap (derivedCospanPresentation p).rightMap
    (derivedCospanPresentation_left p) (derivedCospanPresentation_right p)
    (derivedCospanPresentation_target p)

/-- 概要：任意の cospan から作った標準四角形は ∞ 引き戻し。
方針：N7 の semifree 内の引き戻し性を使う。
規約：追加の cospan 一致条件は不要。使われ方：任意の cospan の極限。 -/
lemma derivedCospanFiberSquare_isPullback
    (p : (horn 2 2 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (derivedCospanFiberSquare p) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFiberSquare_isPullback _ _ _ _ _

/-- 概要：標準四角形の cospan は指定した元の cospan と一致する。
方針：充満包含の単射性で全複体へ移し、標準表示の一致を使う。
規約：単体的な射の厳密な一致。使われ方：極限錐の図式の輸送。 -/
lemma derivedCospanFiberSquare_cospan
    (p : (horn 2 2 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (derivedCospanFiberSquare p) = p := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion (S := S))).1
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (derivedCospanFiberSquare p ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion) =
    p ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion
  rw [derivedCospanFiberSquare, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFiberSquare_inclusion]
  exact (derivedCospanPresentation p).cospan_eq

/-- 概要：D(S) の任意の cospan は極限錐を持つ。
方針：標準 fiber 四角形の錐を元の図式の上へ輸送する。
規約：coslice 側の余極限は仮定しない。使われ方：D7 の全辺の fiber の存在。 -/
lemma derivedInfinityCategory_hasLimit_cospan
    (p : (horn 2 2 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p := by
  let Q := derivedCospanFiberSquare p
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone Q
  let h := (derivedCospanFiberSquare_cospan p).symm
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rebaseCone h c,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rebaseCone_isLimit h c (derivedCospanFiberSquare_isPullback p)⟩

/-- 概要：D(S) の全ての指定した辺は fiber 四角形を持つ。
方針：零頂点と任意の cospan の極限に S1 の fiber 構成を適用する。
規約：入力の辺を四角形の右辺に厳密に保持する。使われ方：IsStable の fiber_exists。 -/
lemma derivedInfinityCategory_fiber_exists {x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)) x y) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare f) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_fiberSquare_of_cospan_limits derivedInfinityCategory_hasLimit_cospan f

end SerrePositivity.InfinityCategories.Project.DerivedCategories
