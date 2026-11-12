module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalReplacementPathIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanHomotopyRectificationImage
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative

/-!
概要：同型で可換な Kan cospan 比較を厳密化するための、底の指定同型を構成する。
方針：元の比較の逆と元の置換 path を合成し、定値切断の終点だけ表示変更する。
規約：与えられた比較同型の値を保持。使われ方：native 四射の比較の厳密化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {X Z X' Z' : SSet.{u}} [KanComplex Z] [KanComplex Z']
  (f : X ⟶ Z) (f' : X' ⟶ Z') (s : X ⟶ X') (v : Z ⟶ Z')
  (e : FunctorIso (f ≫ v) (s ≫ f'))
local notation "pr" => pullback.snd (NatTrans.app (intervalEndpointNatTrans 0) Z) f

/-- 原入力から置換後の入力への候補は、元の指定同型の逆を底に持つ。 -/
def cospanRectificationRightBaseIso :
    FunctorIso ((s ≫ intervalReplacementSection f') ≫ intervalReplacementEndpoint f')
      (f ≫ v) :=
  functorIsoOfEq e.symm
    (by rw [Category.assoc, intervalReplacementSection_endpoint]) rfl

/-- 元の第一置換からの候補は、元の指定同型の逆と元の全 path の合成を底に持つ。 -/
def cospanRectificationLeftBaseIso :
    FunctorIso ((pr ≫ s ≫ intervalReplacementSection f') ≫ intervalReplacementEndpoint f')
      (intervalReplacementEndpoint f ≫ v) := by
  let d := functorIsoOfEq ((intervalReplacementPathIso f).postcomp v)
    (Category.assoc pr f v) rfl
  exact functorIsoOfEq (FunctorIso.precomp e.symm pr ≪≫ d)
    (by simp only [Category.assoc, intervalReplacementSection_endpoint]) rfl

end SerrePositivity.InfinityCategories.F2
