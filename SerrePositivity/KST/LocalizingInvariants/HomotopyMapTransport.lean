module

public import SerrePositivity.KST.LocalizingInvariants.TriangleEdgeHomotopy

/-!
概要：同じ全ホモトピー射の端点を回収し、指定端点へ全射を変えずに輸送する。
方針：両端の制限式を比較し、得た写像の等号でホモトピーを輸送する。
規約：h Fun の像だけから端点を復元しない。使われ方：三角形 prism の正規化。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.HomotopyArrow

variable {A X : SSet.{u}} {F G F' G' : A ⟶ X}

lemma source_eq_of_map_eq (H : SSet.Homotopy F G) (J : SSet.Homotopy F' G')
    (h : H.h = J.h) : F = F' :=
  H.h₀.symm.trans ((congrArg (fun k ↦ SSet.ι₀ ≫ k) h).trans J.h₀)

lemma target_eq_of_map_eq (H : SSet.Homotopy F G) (J : SSet.Homotopy F' G')
    (h : H.h = J.h) : G = G' :=
  H.h₁.symm.trans ((congrArg (fun k ↦ SSet.ι₁ ≫ k) h).trans J.h₁)

def rebase (H : SSet.Homotopy F G) (hF : F = F') (hG : G = G') :
    SSet.Homotopy F' G' := hF ▸ hG ▸ H

lemma rebase_map (H : SSet.Homotopy F G) (hF : F = F') (hG : G = G') :
    (rebase H hF hG).h = H.h := by
  subst F' G'
  rfl

lemma rebase_arrow (H : SSet.Homotopy F G) (hF : F = F') (hG : G = G') :
    Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) =
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (rebase H hF hG))) :=
  congr _ _ (rebase_map H hF hG).symm

end SerrePositivity.KST.LocalizingInvariants.HomotopyArrow
