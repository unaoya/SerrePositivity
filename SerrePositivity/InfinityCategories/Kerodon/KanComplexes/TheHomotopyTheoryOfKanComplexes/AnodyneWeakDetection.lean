module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanSourceReplacement
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 元の anodyne 局所化の同型から Kan 標的による弱同値への判定

概要：元の反転性を F1b の弱ホモトピー同値と弱可縮性へ移す。
方針：全 Kan 標的への内部 Hom の π₀ を反変関手とし、局所化の普遍性で反転する。
規約：元の始域・終域に Kan 性や単体集合モデルを要求しない。
使われ方：分解の comma の可縮性と Quillen A の条件の接続。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v

namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalClosed _root_.Opposite _root_.SSet
open _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.SimplicialModel

/-- 概要：固定した標的への元の写像空間の π₀ は反変関手（Kerodon §3.1.7（Tag 00U1））。
方針：元の内部 Hom の前合成と π₀ の恒等・合成則を使う。
規約：全対象と元の前合成を保持する。
使われ方：局所化における反転性の Kan 標的による検査。 -/
def homComponents (Z : SSet.{v}) : SSet.{v}ᵒᵖ ⥤ Type v where
  obj A := SSet.π₀ ((ihom A.unop).obj Z)
  map f := ↾(SSet.mapπ₀ ((pre f.unop).app Z))
  map_id A := by
    apply ConcreteCategory.hom_ext
    intro x
    change SSet.mapπ₀ ((pre (𝟙 A.unop)).app Z) x = x
    rw [pre_id, NatTrans.id_app, SSet.mapπ₀_id_apply]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    change SSet.mapπ₀ ((pre (g.unop ≫ f.unop)).app Z) x =
      SSet.mapπ₀ ((pre g.unop).app Z) (SSet.mapπ₀ ((pre f.unop).app Z) x)
    rw [pre_map, NatTrans.comp_app, SSet.mapπ₀_comp_apply]

/-- 概要：Kan 標的の同じ反変 π₀ は anodyne 射を反転（Kerodon §3.1.7（Tag 00U1））。
方針：Kan 標的への前合成の実際のホモトピー同値から全単射を得る。
規約：モデル構造や始域の充填性は要求しない。
使われ方：元の anodyne 局所化からの持ち上げ。 -/
lemma homComponents_inverts (Z : SSet.{v}) [KanComplex Z] :
    SSet.anodyneExtensions.IsInvertedBy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.homComponents Z).rightOp := by
  intro A B f hf
  have : IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.homComponents Z).map f.op) :=
    (isIso_iff_bijective _).mpr
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.homotopyEquivalence_pre_of_anodyne f hf Z).mapPiZero_bijective
  change IsIso (((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.homComponents Z).map f.op).op)
  infer_instance

/-- 概要：anodyne 局所化の同じ射の同型性は弱ホモトピー同値を与える（Kerodon §3.1.7（Tag 00U1））。
方針：元の局所化の普遍性を全 Kan 標的の反変 π₀ へ適用する。
規約：元の射の両端に Kan 性を要求しない。
使われ方：Quillen A の弱可縮な slice 条件への接続。 -/
@[kerodon 00UP, kerodon 00ZH, kerodon 00ZJ, kerodon 0104]
lemma isWeakHomotopyEquivalence {A B : SSet.{v}} (f : A ⟶ B)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f := by
  intro Z hZ
  have : IsIso (((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.homComponents Z).map f.op).op) :=
    AnodyneHomotopy.map_isIso_of_anodyneQ_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.homComponents Z).rightOp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.homComponents_inverts Z) f hf
  have : IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.homComponents Z).map f.op) := isIso_of_op _
  exact (isIso_iff_bijective _).mp this

/-- 概要：元の標準零単体への終射の反転性は弱可縮性を与える（Quillen A）。
方針：選ばれた終対象との実同型と元の終射の一意性を使う。
規約：元の単体集合の Kan 性は要求しない。
使われ方：全 comma 圏の可縮性を slice の条件へ移す。 -/
lemma isWeaklyContractible (K : SSet.{v})
    (hK : IsIso (AnodyneHomotopy.anodyneQ.map (SSet.stdSimplex.isTerminalObj₀.from K))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible K := by
  have he : SSet.stdSimplex.isTerminalObj₀.from K ≫
      (SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso terminalIsTerminal).hom = terminal.from K :=
    terminal.hom_ext _ _
  have : IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from K)) := by
    rw [← he, CategoryTheory.Functor.map_comp]
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence (terminal.from K) this

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection
