module

public import SerrePositivity.DifferentialGraded.Algebras.SmallObject
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainComonoid
public import Mathlib.AlgebraicTopology.ModelCategory.PathObject
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# AW path object による転送 acyclicity の入力

概要：実 AW 畳み込み path の二端点を転送の持ち上げ論法へ渡す。
方針：前 path object・二端点の全射性・各端点の擬同型性を明示する。
規約：モデル構造を仮定せず、carrier は実 N(Δ¹) の内部 Hom と照合する。
使われ方：自由 J-cell の底の擬同型性の証明。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DGAlgebra
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]

/-- 概要：元の dg モノイドの有限極限。
方針：忘却が作る極限を指定した有限形ごとに選ぶ。
規約：大域 instance は追加しない。使われ方：path の両端点と終対象。 -/
lemma hasFiniteLimits : HasFiniteLimits (Mon (Complex R)) where
  out J _ _ := Mon.instHasLimitsOfShape (C := Complex R) (J := J)

/-- 概要：元の dg モノイドの二項積。
方針：底の選んだ二項積を忘却で持ち上げる。
規約：局所的に選ぶクラス値。使われ方：二端点の評価対。 -/
lemma hasBinaryProducts : HasBinaryProducts (Mon (Complex R)) := by
  let : HasBinaryProducts (Complex R) :=
    (_root_.SerrePositivity.ProjectiveModel.projectiveModelCategory R).cm1a.out (Discrete WalkingPair)
  exact Mon.instHasLimitsOfShape (C := Complex R) (J := Discrete WalkingPair)
/-- 概要：元の dg モノイドの終対象。
方針：底の選んだ終対象を忘却で持ち上げる。
規約：局所的に選ぶクラス値。使われ方：fibrancy と retraction の持ち上げ。 -/
lemma hasTerminal : HasTerminal (Mon (Complex R)) := by
  let : HasTerminal (Complex R) :=
    (_root_.SerrePositivity.ProjectiveModel.projectiveModelCategory R).cm1a.out (Discrete PEmpty.{1})
  exact Mon.instHasLimitsOfShape (C := Complex R) (J := Discrete PEmpty.{1})

attribute [local instance] _root_.SerrePositivity.DGAlgebra.hasBinaryProducts _root_.SerrePositivity.DGAlgebra.hasTerminal

/-- 概要：元の AW 区間の実 dg 代数 path object に必要な情報。
方針：同じ前 path と底の三つの射性質を束ねる。
規約：単体集合のモデル構造は含めない。
使われ方：具体的な AW 畳み込みを代入して実転送を得る。 -/
structure AWPathInput where
  /-- 元の dg 代数の前 path object。 -/
  path (B : Mon (Complex R)) : PrepathObject B
  /-- 底は実 AW 区間からの内部 Hom。 -/
  carrier (B : Mon (Complex R)) : ((path B).P).X ≅
    homComplex R (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains R (Δ[1] : SSet.{0})) B.X
  /-- 二端点を同時に指定できる。 -/
  pair_fibration (B : Mon (Complex R)) : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations R ((path B).p).hom
  /-- 零端点評価の擬同型性。 -/
  first_quasiIso (B : Mon (Complex R)) : QuasiIso ((path B).p₀).hom
  /-- 一端点評価の擬同型性。 -/
  second_quasiIso (B : Mon (Complex R)) : QuasiIso ((path B).p₁).hom

/-- 概要：元の dg 代数から終対象への射は底で次数別全射。
方針：忘却と各次数の評価が終対象を保つことから零加群性を使う。
規約：代数のモデル構造を使わない。
使われ方：acyclicity の鎖 retraction を持ち上げる。 -/
lemma terminalFrom_projectiveFibration (B : Mon (Complex R)) :
    _root_.SerrePositivity.ProjectiveModel.projectiveFibrations R (terminal.from B).hom := by
  intro n y
  let F := Mon.forget (Complex R) ⋙ eval (ModuleCat.{u} R) (.up ℤ) n
  have ht : IsTerminal (F.obj (⊤_ (Mon (Complex R)))) :=
    terminalIsTerminal.isTerminalObj F
  have hz : IsZero (F.obj (⊤_ (Mon (Complex R)))) :=
    (isZero_zero (ModuleCat.{u} R)).of_iso
      (ht.uniqueUpToIso (isZero_zero (ModuleCat.{u} R)).isTerminal)
  have hsub : Subsingleton (((⊤_ (Mon (Complex R))).X).X n) :=
    ModuleCat.subsingleton_of_isZero hz
  exact ⟨0, hsub.elim _ _⟩

end SerrePositivity.DGAlgebra
