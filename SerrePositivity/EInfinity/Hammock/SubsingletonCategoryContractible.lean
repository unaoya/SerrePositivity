module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SubsingletonCategoryRows
public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection

/-!
# 一対象で薄い元の圏の hammock の終対象性

概要：元の全語の余極限は単体集合の終対象となる。
方針：空語からの単位点と全点の回収式で元の射の一意性を示す。
規約：任意の乗法的な指定矢の類を許す。
使われ方：有限木の根だけの基底。
-/

@[expose] public section
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.SubsingletonCategory
open CategoryTheory Limits MonoidalCategory SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [Subsingleton C] [Quiver.IsThin C]
  (W : MorphismProperty C) [W.IsMultiplicative]

def toUnit (A : SSet.{w}) : A ⟶ 𝟙_ SSet.{w} where
  app _ := ↾fun _ => PUnit.unit
  naturality _ _ _ := rfl

def colimit_isTerminal (X Y : C) : IsTerminal (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y) := by
  have h : X = Y := Subsingleton.elim _ _
  subst Y
  refine IsTerminal.ofUniqueHom (fun A => toUnit.{max u v} A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W X) ?_
  intro A f
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SubsingletonCategoryRows.colimit_point_eq_unit X n (f.app n p)

lemma colimit_isWeaklyContractible (X Y : C) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y) := by
  let e := (colimit_isTerminal W X Y).uniqueUpToIso terminalIsTerminal
  have he : e.hom = terminal.from (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y) := terminal.hom_ext _ _
  have hi : IsIso (terminal.from (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y)) := he ▸ e.isIso_hom
  exact FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _ (by infer_instance)

end SerrePositivity.EInfinity.Hammock.SubsingletonCategory
