module

public import SerrePositivity.KST.Spectra.PointedPrecompositionSourceNaturality
public import SerrePositivity.KST.Spectra.SquareBoundaryFamilies

/-!
概要：入力を動かす実区間を、固定した写像区間へ作用させる二次元正方形。
方針：入力区間の前合成ホモトピーへ、元の区間の実辺を前合成する。
規約：二つの区間全体を保持。使われ方：延長切断の比較から交換の自然性正方形を作る。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping.VerticalPath

/-- 入力区間を固定した区間の全実辺に作用させた、同じ二次元正方形。 -/
def inputSquare {A B E C : PointedSimplicialSet.{u}} {p : B ⟶ C}
    {a b : A ⟶ B} (H : VerticalPath p a b) {f g : B ⟶ E}
    (P : VerticalPath (PointedObject.toPoint E) f g) :
    SSet.Homotopy (P.pre a).path (P.pre b).path where
  h := P.path ▷ (Δ[1] : SSet.{u}) ≫ (H.forgetProjection.basedPre E).homotopy.h
  h₀ := by
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc,
      (H.forgetProjection.basedPre E).homotopy.h₀]
    rfl
  h₁ := by
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc,
      (H.forgetProjection.basedPre E).homotopy.h₁]
    rfl
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

end SerrePositivity.KST.Spectra.PointedMapping.VerticalPath
