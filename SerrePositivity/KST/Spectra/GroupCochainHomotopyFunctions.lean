module

public import SerrePositivity.KST.Spectra.FreePointedFunctionHomotopy
public import SerrePositivity.KST.Spectra.PointedActionHomotopy
public import SerrePositivity.KST.Spectra.GroupCoefficientCochains

/-!
概要：群 cochain の正次数ホモトピー群の余単体図式と係数のホモトピー群の非斉次 cochain の同型。
方針：点つき関数複体の各座標の π_* の同型と前合成の座標式を束ねる。
規約：全ての顔・退化を保つ群の圏の自然同型。
使われ方：Goerss–Jardine I §7、VIII §2。有理 cochain の代数的な計算への比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：非斉次関数複体の正次数 π_* は係数の群の非斉次 cochain 図式と自然に同型。
方針：座標ごとの群同型を前合成の π_* の座標式で束ねる。
規約：係数の作用は各群元の点つき射が π_* に誘導する作用。
使われ方：Goerss–Jardine VIII §2。単体的 cochain の群の係数への移送。 -/
def GroupActionCochains.functionHomotopyNatIso {G : Type u} [Group G]
    (B : Action PointedSimplicialSet.{u} G) [KanComplex B.V.right] (k : ℕ) :
    KanHomotopyGroup.diagram (pointedFunctionCochains B) k ≅
      GroupCoefficientCochains.obj (PointedActionCochains.homotopyAction B k) :=
  NatIso.ofComponents
    (fun n ↦ MulEquiv.toGrpIso
      (X := (KanHomotopyGroup.diagram (pointedFunctionCochains B) k).obj n)
      (Y := (GroupCoefficientCochains.obj (PointedActionCochains.homotopyAction B k)).obj n)
      (SimplicialFunctionComplex.pointedHomotopyEquiv (Fin n.len → G) B.V k))
    (fun f ↦ by
      ext a
      funext t
      exact FreeActionFamily.pointedFunctionPre_homotopy_coordinate
        ((freeUniversalCover G).map f.op) B k a t)

/-- 概要：群 cochain の正次数 π_* の余単体群は係数の π_* の非斉次 cochain と自然に同型。
方針：cochain 全体の点つき非斉次比較と関数複体の座標ごとの π_* の比較を合成する。
規約：k は実際の次数 k+1。非可換な π_1 も含めて群の図式の同型を与える。
使われ方：Goerss–Jardine I §7、VIII §2。群 cohomology と Tot の π_* の橋渡しの代数側の入力。 -/
def PointedActionCochains.homotopyFunctionNatIso {G : Type u} [Group G]
    (B : Action PointedSimplicialSet.{u} G) [KanComplex B.V.right] (k : ℕ) :
    KanHomotopyGroup.diagram (obj B) k ≅
      GroupCoefficientCochains.obj (homotopyAction B k) :=
  homotopyDiagramIso B k ≪≫ GroupActionCochains.functionHomotopyNatIso B k

end

end SerrePositivity.KST.Spectra
