module

public import SerrePositivity.EInfinity.SimplexCuts.CutHeights
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalDeletion

/-!
# nullaryの一頂点区間の同じ水平辺の挿入・削除

Berger–Fresse §1.1.3・§2.2.6、M14 L12a の有限対応、報告 §318。
既存horizontalInsertionEquivと元の水平辺の昇順番号を使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts


def nullaryPointEraseCut {m q : ℕ} (s : Cut (m + 1) q) (p : Fin (m + 2)) : Cut m q :=
  let i : Fin (m + 1) := ⟨min p.val m, by have h := Nat.min_le_right p.val m; omega⟩
  (BarrattEccles.horizontalInsertionEquiv m q (cutHorizontalEdge s i)).symm
    ⟨s, s.val.orderEmbOfFin_mem s.property i⟩

def nullaryPointInsertionEdge {m q : ℕ} (t : Cut m q) (p : Fin (m + 2)) :
    Fin (m + 1 + q) :=
  if hzero : p.val = 0 then ⟨0, by omega⟩
  else if htop : p.val = m + 1 then ⟨m + q, by omega⟩
  else
    let i : Fin m := ⟨p.val - 1, by have hp := p.isLt; omega⟩
    ⟨(cutHorizontalEdge t i).val + 1, by have hb := (cutHorizontalEdge t i).isLt; omega⟩

def nullaryPointInsertCut {m q : ℕ} (t : Cut m q) (p : Fin (m + 2)) : Cut (m + 1) q :=
  (BarrattEccles.horizontalInsertionEquiv m q (nullaryPointInsertionEdge t p) t).val


end SerrePositivity.EInfinity.SimplexCuts
