module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.CompositionTriangleSpace
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：同じパラメーター付き内ホーンを厳密に固定する全充填空間と、その中の比較。
方針：内ホーンと任意の単体集合の積を inner anodyne とし、制限の自明 Kan fiber を取る。
規約：欠面の指定はこの補題の結論に含めず、固定する全ホーンは同じものを使う。
使われ方：Ind-S (9) の同じ三面内の比較と (9b) の全族充填。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 同じパラメーター付きホーンを固定した、実際の全充填空間。 -/
def innerHornFamilyExtensionSpace {X : SSet.{u}} (n : ℕ) (i : Fin (n + 1))
    (K : SSet.{u}) (b : (horn n i : SSet.{u}) ⊗ K ⟶ X) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre ((horn n i).ι ▷ K)).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b)

/-- 同じ内ホーン全族の実充填空間は可縮 Kan。 -/
lemma innerHornFamilyExtensionSpace_isContractibleKan {X : SSet.{u}} [Quasicategory X]
    (n : ℕ) (i : Fin (n + 1)) (hi₀ : 0 < i) (hiₙ : i < Fin.last n)
    (K : SSet.{u}) (b : (horn n i : SSet.{u}) ⊗ K ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (innerHornFamilyExtensionSpace n i K b) := by
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre ((horn n i).ι ▷ K)).app X) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne _
      ((innerAnodyneExtensions.horn_ι hi₀ hiₙ).whiskerRight K) X
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan _ _

/-- 元のホーン全族の実充填を構成し、制限を厳密に回収する。 -/
lemma innerHornFamily_exists_extension {X : SSet.{u}} [Quasicategory X]
    (n : ℕ) (i : Fin (n + 1)) (hi₀ : 0 < i) (hiₙ : i < Fin.last n)
    (K : SSet.{u}) (b : (horn n i : SSet.{u}) ⊗ K ⟶ X) :
    ∃ F : (Δ[n] : SSet.{u}) ⊗ K ⟶ X, ((horn n i).ι ▷ K) ≫ F = b := by
  have := ((innerAnodyneExtensions.horn_ι hi₀ hiₙ).whiskerRight K)
    (terminal.from X) (InnerFibration.mem (q := terminal.from X))
  let sq : CommSq b ((horn n i).ι ▷ K) (terminal.from X) (terminal.from _) :=
    ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 指定した同じ三面の充填空間内で、元の充填と制御充填を比較する。 -/
lemma tetrahedronFamilyExtensionSpace_compare {X : SSet.{u}} [Quasicategory X]
    (K : SSet.{u}) (b : (Λ[3, 2] : SSet.{u}) ⊗ K ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (innerHornFamilyExtensionSpace 3 2 K b) ∧
      ∀ old controlled : (innerHornFamilyExtensionSpace 3 2 K b) _⦋0⦌,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso old controlled) := by
  have hc := innerHornFamilyExtensionSpace_isContractibleKan 3 2 (by decide) (by decide) K b
  have := hc.kanComplex
  exact ⟨hc, fun old controlled =>
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso (hc.isTerminalVertex old) (hc.isTerminalVertex controlled)⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
