module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramCategory
public import SerrePositivity.KST.LocalizingInvariants.ProSpectrumValues

/-!
概要：実 fiber 図式の塔と、元の三対象・包含・射影の pro 値。
方針：全正方形の比較を評価する関手を既存の Tower・LevelHom へ適用する。
規約：各段の接続射を保持し、ProFiberConnecting でレベル射へ昇格する。
使われ方：自然な長完全列と pro 切除の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants

abbrev ProFiberSequence := ProExcision.Tower FiberDiagram.{u}

namespace ProFiberSequence
variable (D : ProFiberSequence.{u})

def vertex (i j : Fin 2) : ProSpectrum.Tower.{u} := D.map (FiberDiagram.vertex i j)

def inclusion : ProSpectrum.LevelHom (vertex D 0 0) (vertex D 1 0) where
  app n := FiberDiagram.inclusion.app (D.obj n)
  naturality h := FiberDiagram.inclusion.naturality (D.transition h)

def projection : ProSpectrum.LevelHom (vertex D 1 0) (vertex D 1 1) where
  app n := FiberDiagram.projection.app (D.obj n)
  naturality h := FiberDiagram.projection.naturality (D.transition h)

def groups (i k : Fin 2) (j : ℤ) : ProExcision.Tower CommGrpCat.{u} :=
  ProSpectrum.groups (vertex D i k) j

def groupInclusion (j : ℤ) : ProExcision.LevelHom (groups D 0 0 j) (groups D 1 0 j) :=
  (inclusion D).map (SpectrumHo.piFunctor j)

def groupProjection (j : ℤ) : ProExcision.LevelHom (groups D 1 0 j) (groups D 1 1 j) :=
  (projection D).map (SpectrumHo.piFunctor j)

def connecting (n : ℕ) (j : ℤ) : (groups D 1 1 (j + 1)).obj n ⟶ (groups D 0 0 j).obj n :=
  CommGrpCat.ofHom (NativeFiber.boundary (D.obj n).triangle (D.obj n).isFiber j)

lemma exact_fiber (n : ℕ) (j : ℤ) (x : (groups D 0 0 j).obj n) :
    ((groupInclusion D j).app n).hom x = 1 ↔
      ∃ y : (groups D 1 1 (j + 1)).obj n, (connecting D n j).hom y = x :=
  NativeFiber.exact_fiber (D.obj n).triangle (D.obj n).isFiber j x

lemma exact_total (n : ℕ) (j : ℤ) (x : (groups D 1 0 j).obj n) :
    ((groupProjection D j).app n).hom x = 1 ↔
      ∃ y : (groups D 0 0 j).obj n, ((groupInclusion D j).app n).hom y = x :=
  NativeFiber.exact_total (D.obj n).triangle (D.obj n).isFiber j x

lemma exact_base (n : ℕ) (j : ℤ) (x : (groups D 1 1 (j + 1)).obj n) :
    (connecting D n j).hom x = 1 ↔ ∃ y : (groups D 1 0 (j + 1)).obj n,
      ((groupProjection D (j + 1)).app n).hom y = x :=
  NativeFiber.exact_base (D.obj n).triangle (D.obj n).isFiber j x

end ProFiberSequence
end SerrePositivity.KST.LocalizingInvariants

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Eq (1.2)" (partial := component) "仮定：すでにレベルごとのファイバー列を与える（Lean が強い）。結論：各次数の境界と完全性。抽象ブローアップの非連結 K の四角形からこの列を得る部分は別（Lean が弱い）。"] _root_.SerrePositivity.KST.LocalizingInvariants.ProFiberSequence.exact_base
attribute [cite KST "Eq (1.2)" (partial := component) "仮定：すでにレベルごとのファイバー列を与える（Lean が強い）。結論：各次数の境界と完全性。抽象ブローアップの非連結 K の四角形からこの列を得る部分は別（Lean が弱い）。"] _root_.SerrePositivity.KST.LocalizingInvariants.ProFiberSequence.exact_fiber
attribute [cite KST "Eq (1.2)" (partial := component) "仮定：すでにレベルごとのファイバー列を与える（Lean が強い）。結論：各次数の境界と完全性。抽象ブローアップの非連結 K の四角形からこの列を得る部分は別（Lean が弱い）。"] _root_.SerrePositivity.KST.LocalizingInvariants.ProFiberSequence.exact_total
attribute [cite KST "Eq (6.1)" (partial := component) "仮定：レベルごとのファイバー列を指定する（Lean が強い）。結論：各次数の列の完全性。Δ^j 上の具体的な双相対 K のファイバーの三項を構成しない（Lean が弱い）。"] _root_.SerrePositivity.KST.LocalizingInvariants.ProFiberSequence.exact_fiber
attribute [cite KST "Eq (6.1)" (partial := component) "仮定：レベルごとのファイバー列を指定する（Lean が強い）。結論：各次数の列の完全性。Δ^j 上の具体的な双相対 K のファイバーの三項を構成しない（Lean が弱い）。"] _root_.SerrePositivity.KST.LocalizingInvariants.ProFiberSequence.exact_total
