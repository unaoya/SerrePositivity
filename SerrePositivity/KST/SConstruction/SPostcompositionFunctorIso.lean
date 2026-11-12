module
public import SerrePositivity.KST.SConstruction.FullSubcomplexFunctorIsoReflection
public import SerrePositivity.KST.SConstruction.StableModels
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorComposition

/-! # S_n の後合成による関手同型の保存
概要：完全関手の coherent な同型を、S_n 上の元の後合成の関手同型に移す。
方針：内部 Hom の後合成で同型を写し、gapped 全部分複体の包含で反映する。
規約：単体的射の関手同型そのもの。使われ方：反復実現による完全同値の保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories

/-- S_n の元の完全な後合成は完全関手の関手同型を保つ。 -/
def sPostcompositionFunctorIso (n : ℕ) {X Y : StableModel.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f.val g.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((sEndofunctor n).map f).val ((sEndofunctor n).map g).val := by
  apply functorIsoOfFullSubcomplexPostcomp
    (fun v => IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) Y.carrier).symm v))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (sPostcompCofiber n f.val f.property ≫ (gappedSubcomplex n Y.carrier).ι)
    (sPostcompCofiber n g.val g.property ≫ (gappedSubcomplex n Y.carrier).ι)
  rw [sPostcompCofiber_ι, sPostcompCofiber_ι]
  exact (e.map_post (arNerve n)).precomp (gappedSubcomplex n X.carrier).ι

end SerrePositivity.KST.SConstruction
