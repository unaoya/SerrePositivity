module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeCofiberZeroTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberSuspensionSquareHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FullFunctorHomotopyLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SuspensionSquareHomotopy

/-! # Semifree 内の cofiber から suspension への四角形比較射

概要：全複体で構成した二段比較を Semifree 内の関手圏の h の射へ持ち上げる。
方針：両端を包含像に正規化し、充満 dg 部分圏への図式射の持ち上げを使う。
規約：包含後の射を Arrow の等式で保持する。使われ方：D7 の実際の接続射の計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial ZeroObject
variable {S : Type u} [CommRing S] {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}

/-- 両端を Semifree の包含像に合わせた周囲の cofiber 比較射。 -/
def cofiberSuspensionHomOnInclusion (f : X.val ⟶ Y.val) :
    (SSet.HomotopyCategory.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f).square ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)) :
        hoFunctor.obj ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)))) ⟶
      SSet.HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).square ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenEqToHom (congrArg (fun F => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_inclusion f)) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionSquareHom f ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenEqToHom (congrArg (fun F => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare_inclusion X).symm)

/-- Semifree 内の cofiber 四角形から標準 suspension 四角形への実際の図式射。 -/
def semifreeCofiberSuspensionHom (f : X.val ⟶ Y.val) :
    (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f).square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S))) ⟶
      SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).square) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.exists_fullInclusion_functorHom S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f).square (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).square
    (cofiberSuspensionHomOnInclusion f))

/-- 持ち上げた比較射の包含像は周囲で構成した二段比較。 -/
lemma semifreeCofiberSuspensionHom_inclusion_arrow (f : X.val ⟶ Y.val) :
    Arrow.mk ((hoFunctor.map ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)).toFunctor.map (semifreeCofiberSuspensionHom f)) =
      Arrow.mk (cofiberSuspensionHomOnInclusion f) :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.exists_fullInclusion_functorHom S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f).square (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).square
    (cofiberSuspensionHomOnInclusion f))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
