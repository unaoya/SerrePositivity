module
public import SerrePositivity.KST.Fibration.RelativeSQuotientRealization
public import SerrePositivity.KST.Fibration.RelativeSKernelSimplicialIso
public import SerrePositivity.KST.Fibration.SComponentExactness
public import SerrePositivity.KST.SConstruction.CoreSimplicial
public import SerrePositivity.KST.SConstruction.ReductionEquivalence

/-!
概要：商比較の零段を無条件で処理し、実現比較の残入力を正の段に限定する。
方針：S₀ の全図式の零性と core S₀ の可縮性を、元の商射影に適用する。
規約：正の段の図式局所化は Sp 正本の明示入力として保持する。
使われ方：K-6 c5 の同じ相対 S• 商実現比較。
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

/-- 完全商関手に関する零段の相対条件は、全ての元の S₀ 図式で成立する。 -/
theorem relativeSQuotient_zero_eq_top {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    relativeSConstruction q.hom 0 = ⊤ := by
  apply relativeDiagram_eq_top_of_zero
  intro a x
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := q.hom) _
    ((sConstruction_isZeroVertex_iff_components B.obj 0 x).mp
      (sConstructionZero_isZeroVertex B.obj x) a)

/-- 元の零段の商射影そのものは anodyne 局所化で可逆。 -/
theorem relativeSQuotient_zero_localized_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeSQuotientMap q 0)) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  let e : (relativeSConstruction q.hom 0 : SSet.{u}) ≅ sConstruction 0 B.obj :=
    eqToIso (congrArg (fun P : (sConstruction 0 B.obj).Subcomplex => (P : SSet.{u}))
      (relativeSQuotient_zero_eq_top q)) ≪≫ Subcomplex.topIso _
  have hb := initialVertex_toPoint_localized_isIso
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex (sConstruction 0 B.obj)).isZero.1
  have he : e.hom ≫ terminal.from _ = terminal.from _ := terminal.hom_ext _ _
  have hs : IsIso (Q.map (terminal.from (relativeSConstruction q.hom 0 : SSet.{u}))) := by
    rw [← he, Functor.map_comp]
    infer_instance
  let T := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction 0 C.obj) : SSet.{u})
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (toUnit T) :=
    trivialKanFibration_toUnit_of_contractible (coreSConstructionZero_isContractibleKan C.obj)
  have hu := map_isIso_of_trivialKanFibration Q
    (Localization.inverts Q anodyneExtensions) (toUnit T)
  have hi : IsIso (terminal.from (𝟙_ SSet.{u})) :=
    isIso_of_isTerminal isTerminalTensorUnit terminalIsTerminal _
  have ht : IsIso (Q.map (terminal.from T)) := by
    have ht : toUnit T ≫ terminal.from (𝟙_ SSet.{u}) = terminal.from T := terminal.hom_ext _ _
    rw [← ht, Functor.map_comp]
    infer_instance
  have hf : relativeSQuotientMap q 0 ≫ terminal.from T = terminal.from _ := terminal.hom_ext _ _
  have hc : IsIso (Q.map (relativeSQuotientMap q 0) ≫ Q.map (terminal.from T)) := by
    rw [← Functor.map_comp, hf]
    exact hs
  exact (isIso_comp_right_iff _ _).mp hc

/-- 零段は自動であり、正の段だけの同じ商比較から元の実現比較を得る。 -/
theorem relativeSQuotientRealization_localized_isIso_of_positive_stages
    {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (hq : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map (relativeSQuotientMap q (n + 1)))) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (simplicialDiagonalFunctor.map (relativeSimplicialQuotientMap q))) := by
  apply relativeSQuotientRealization_localized_isIso_of_stages
  intro n
  cases n with
  | zero => exact relativeSQuotient_zero_localized_isIso q
  | succ n => exact hq n

end SerrePositivity.KST.Fibration
