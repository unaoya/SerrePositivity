module

public import SerrePositivity.KST.Spectra.PointedActionCochains
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FunctionComplexHomotopyGroups

/-!
概要：点つき群作用の cochain の各次数の正次数ホモトピー群の関数群による表示。
方針：自由軌道の end、離散集合を源とする内部 Hom、関数複体の三つの比較を合成する。
規約：任意の群と任意の基点を許す。余単体構造との整合性は別に扱う。
使われ方：Goerss–Jardine I §7、VIII §2。有限群の有理 cochain の π_* 計算の入力。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.PointedActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：群 cochain の各次数の基礎単体集合は非斉次座標の関数複体と同型。
方針：EG の自由軌道の比較の後、自由基点を除き、内部 Hom を関数複体へ移す。
規約：余単体次数 n の添字集合は Fin n → G。
使われ方：Goerss–Jardine VIII §2。各 cochain 次数の π_* の座標表示。 -/
def functionIso {G : Type u} [Group G] (B : Action PointedSimplicialSet.{u} G) (n : ℕ) :
    ((obj B).obj (SimplexCategory.mk n)).right ≅
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj (Fin n → G) B.V.right :=
  PointedSimplicialSet.forget.mapIso (freeIso B n) ≪≫
    PointedWeightedEnd.underlyingIso (FreeActionFamily.weight (Fin n → G))
      (FreeActionFamily.pointedCoefficients B) ≪≫
    FreeActionFamily.endIso (Fin n → G) ((PointedSimplicialSet.forget.mapAction G).obj B) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom.iso (Fin n → G) B.V.right

/-- 概要：群 cochain の各次数の正次数ホモトピー群は係数の群の関数群と同型。
方針：各次数の関数複体の同型と関数複体のホモトピー群の同型を合成する。
規約：k は実際の次数 k+1。像の基点は各関数座標で読む。
使われ方：Goerss–Jardine I §7、VIII §2。有理群 cochain の係数の群との比較。 -/
def homotopyFunctionEquiv {G : Type u} [Group G] (B : Action PointedSimplicialSet.{u} G)
    [KanComplex B.V.right] (n k : ℕ) (x : ((obj B).obj (SimplexCategory.mk n)).right _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((obj B).obj (SimplexCategory.mk n)).right k x ≃*
      (∀ s : Fin n → G, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B.V.right k ((functionIso B n).hom.app _ x s)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso k (functionIso B n) rfl).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.homotopyEquiv (Fin n → G) B.V.right k
      ((functionIso B n).hom.app _ x))

end

end SerrePositivity.KST.Spectra.PointedActionCochains
