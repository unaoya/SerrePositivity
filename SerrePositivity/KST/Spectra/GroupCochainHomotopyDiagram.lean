module

public import SerrePositivity.KST.Spectra.PointedGroupFunctionCochains
public import SerrePositivity.KST.Spectra.PointedHomotopyGroupDiagram
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FunctionComplexHomotopyGroups

/-!
概要：群 cochain の正次数 π_* の余単体群の図式と非斉次関数図式への比較。
方針：点つき cochain の自然同型に正次数ホモトピー群を適用する。
規約：群の圏の実際の余単体図式の同型を与える。
使われ方：Goerss–Jardine I §7、VIII §2。cochain の π_* の顔・退化の群への移送。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

instance SimplicialFunctionComplex.pointedObj_kanComplex (S : Type u)
    (X : PointedSimplicialSet.{u}) [KanComplex X.right] :
    KanComplex (pointedObj S X).right :=
  inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S X.right))

instance GroupActionCochains.pointedFunctionCochains_kanComplex {G : Type u} [Group G]
    (B : Action PointedSimplicialSet.{u} G) [KanComplex B.V.right] (n : SimplexCategory) :
    KanComplex ((pointedFunctionCochains B).obj n).right :=
  inferInstanceAs (KanComplex (SimplicialFunctionComplex.pointedObj (Fin n.len → G) B.V).right)

/-- 概要：群 cochain の正次数 π_* は非斉次関数複体の π_* の余単体群と自然に同型。
方針：点つき cochain の余単体自然同型をホモトピー群の図式へ送る。
規約：k は実際の次数 k+1。全ての顔・退化に自然。
使われ方：Goerss–Jardine I §7、VIII §2。有理 cochain の代数的な図式への比較の入力。 -/
def PointedActionCochains.homotopyDiagramIso {G : Type u} [Group G]
    (B : Action PointedSimplicialSet.{u} G) [KanComplex B.V.right] (k : ℕ) :
    KanHomotopyGroup.diagram (obj B) k ≅
      KanHomotopyGroup.diagram (GroupActionCochains.pointedFunctionCochains B) k :=
  KanHomotopyGroup.diagramIso (functionNatIso B) k

/-- 概要：点つき関数複体の標準基点での正次数 π_* は係数の群の関数群と同型。
方針：基点は定義上の定数関数であり、座標ごとのホモトピー群の同型を使う。
規約：k は実際の次数 k+1。
使われ方：Goerss–Jardine I §7、VIII §2。余単体群の各対象の具体的な表示。 -/
def SimplicialFunctionComplex.pointedHomotopyEquiv (S : Type u)
    (X : PointedSimplicialSet.{u}) [KanComplex X.right] (k : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedObj S X).right k (pointedObj S X).basepoint ≃*
      (S → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X.right k X.basepoint) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.homotopyEquiv S X.right k (fun _ ↦ X.basepoint)

end

end SerrePositivity.KST.Spectra
