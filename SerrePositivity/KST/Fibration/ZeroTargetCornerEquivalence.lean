module
public import SerrePositivity.KST.Fibration.ZeroTargetFullSMap
public import SerrePositivity.KST.Fibration.ZeroCategorySRealization
public import SerrePositivity.KST.Fibration.RelativeSKernelDiagonalContraction

/-!
概要：指定零値完全関手から作った元の相対核の角比較の可逆性。
方針：両角の実現から一点への実射を使い、同じ比較写像を局所化で反映する。
規約：抽象的な終対象間同型へ写像を取り替えない。
使われ方：指定 Verdier 左辺を保つ商核四角形の角の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 零圏の元の core S_n は可縮 Kan 複体。 -/
theorem coreSZeroTarget_isContractibleKan (Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
    (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory Z) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n Z.obj) : SSet.{u}) := by
  have hc := allZeroVertices_isContractibleKan (sConstruction n Z.obj) (fun v => by
    apply (sConstruction_isZeroVertex_iff_components _ n v).mpr
    intro a
    exact hZ _)
  let := hc.kanComplex
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso (kanCoreIso _) hc

/-- 零圏の元の一回の core S• 実現の一点射は可逆。 -/
theorem coreSZeroTarget_toPoint_localized_isIso (Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
    (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory Z) :
    IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from
      (simplicialDiagonalFunctor.obj
        (simplicialSConstruction Z.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor)))) := by
  let F := simplicialSConstruction Z.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor
  let c := simplicialSpaceToPoint F
  have hd : IsIso (AnodyneHomotopy.anodyneQ.map (simplicialDiagonalFunctor.map c)) := by
    apply BisimplicialModel.localized_diagonal_map
    intro n
    letI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (toUnit (F.obj n)) :=
      trivialKanFibration_toUnit_of_contractible
        (coreSZeroTarget_isContractibleKan Z hZ n.unop.len)
    have ht : IsIso (terminal.from (𝟙_ SSet.{u})) :=
      isIso_of_isTerminal isTerminalTensorUnit terminalIsTerminal _
    have he : toUnit (F.obj n) ≫ terminal.from (𝟙_ SSet.{u}) =
        terminal.from (F.obj n) := terminal.hom_ext _ _
    change IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from (F.obj n)))
    rw [← he, Functor.map_comp]
    have := map_isIso_of_trivialKanFibration AnodyneHomotopy.anodyneQ
      (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions) (toUnit (F.obj n))
    infer_instance
  have he : simplicialDiagonalFunctor.map c ≫ (constantSSetDiagonalIso (⊤_ SSet.{u})).hom =
      terminal.from (simplicialDiagonalFunctor.obj F) := terminal.hom_ext _ _
  change IsIso (AnodyneHomotopy.anodyneQ.map
    (terminal.from (simplicialDiagonalFunctor.obj F)))
  rw [← he, Functor.map_comp]
  infer_instance

/-- 元の指定零値関手で作った核角比較の実現射そのものが可逆。 -/
theorem relativeSZeroTargetCornerMap_localized_isIso
    {A B C Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A Z) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory Z) :
    IsIso (AnodyneHomotopy.anodyneQ.map (simplicialDiagonalFunctor.map
      (relativeSZeroTargetCornerMap (i.hom ≫ q.hom) f hZ))) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  let g := simplicialDiagonalFunctor.map
    (relativeSZeroTargetCornerMap (i.hom ≫ q.hom) f hZ)
  have hs := relativeSKernelDiagonal_toPoint_localized_isIso h
  have ht := coreSZeroTarget_toPoint_localized_isIso Z hZ
  have he : g ≫ terminal.from _ = terminal.from _ := terminal.hom_ext _ _
  have hc : IsIso (Q.map g ≫ Q.map (terminal.from _)) := by
    rw [← Functor.map_comp, he]
    exact hs
  exact (isIso_comp_right_iff _ _).mp hc

end SerrePositivity.KST.Fibration
