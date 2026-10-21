module

public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramBoundaryNaturality
public import SerrePositivity.KST.LocalizingInvariants.ProFiberSequence

/-!
概要：実 fiber 図式の塔の各段の接続射を、自然な群のレベル射へ昇格する。
方針：任意の全正方形比較について証明した接続射の自然性を、元の遷移へ適用する。
規約：段ごとの既存 connecting を保持。使われ方：全整数長完全列と pro 同値判定。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.ProFiberSequence

variable (D : ProFiberSequence.{u})

def connectingHom (j : ℤ) : ProExcision.LevelHom (groups D 1 1 (j + 1)) (groups D 0 0 j) where
  app n := connecting D n j
  naturality h := by
    ext x
    exact (FiberDiagram.boundary_natural (D.transition h) j x).symm

lemma connectingHom_app (n : ℕ) (j : ℤ) : (connectingHom D j).app n = connecting D n j := rfl

end SerrePositivity.KST.LocalizingInvariants.ProFiberSequence
