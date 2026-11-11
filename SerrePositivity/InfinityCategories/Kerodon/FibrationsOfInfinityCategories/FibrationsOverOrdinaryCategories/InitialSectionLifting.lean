module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialSectionEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialSectionBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：始対象での cocartesian section の評価は自明 Kan fibration。
方針：直積上の相対延長を section の族へ curry し、全ての境界持ち上げを与える。
規約：同値性は評価射そのものについて示す。
使われ方：一般の strict transport と元の fiber の比較。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.InitialSectionLifting

/-- 概要：評価先の頂点 fiber は quasicategory。
方針：inner fibration の fiber の充填性を使う。
規約：同値の型を述べるための局所 instance。
使われ方：評価射の ∞ 圏同値の構成。 -/
local instance {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p] (v : B _⦋0⦌) :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p v) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiber_quasicategory_of_innerFibration p v

/-- 概要：始対象での評価は任意の部分パラメータ上の section を固定して持ち上げる。
方針：族の評価の可換性を実際の図式へ移し、境界と評価を同時に固定して延長する。
規約：部分パラメータは任意の部分複体。
使われ方：自明 Kan fibration の境界持ち上げの構成。 -/
lemma exists_kanCocartesianSectionsEvaluate_lift_of_fixedPrism
    {A T E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (a : A ⟶ B) (v : A _⦋0⦌)
    (hC : ∃ C : (Δ[1] : SSet.{u}) ⊗ A ⟶ A,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ C = SSet.const v ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ C = 𝟙 A ∧
      ∀ K : SSet.{u}, (Δ[1] ◁ (SSet.const v : K ⟶ A)) ≫ C = SSet.const v)
    (U : T.Subcomplex) (g : (U : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a)
    (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (a.app (Opposite.op ⦋0⦌) v))
    (h : g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsEvaluate p a v = U.ι ≫ f) :
    ∃ s : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a,
      U.ι ≫ s = g ∧ s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsEvaluate p a v = f := by
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (a.app (Opposite.op ⦋0⦌) v)
  have hfp : (f ≫ j) ≫ p = SSet.const (a.app (Opposite.op ⦋0⦌) v) := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
  have hGi : lift (SSet.const v) (𝟙 (U : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry g =
      U.ι ≫ f ≫ j := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry_evaluate, ← Category.assoc, h, Category.assoc]
  obtain ⟨F, hFp, hFb, hFi, hFc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.exists_kanSectionTransport_relative_of_fixedPrism p a v hC U
    (f ≫ j) hfp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry_projection g) hGi
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry_cocartesian g)
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsCurry F hFp hFc
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry s = F := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry_curry F hFp hFc
  refine ⟨s, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry_injective p a
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry_precomp, hs, hFb]
  · apply (cancel_mono j).1
    rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry_evaluate, hs, hFi]

/-- 概要：始対象での評価は任意の部分パラメータ上の section を固定して持ち上げる。
方針：族の評価の可換性を実際の図式へ移し、境界と評価を同時に固定して延長する。
規約：部分パラメータは任意の部分複体。
使われ方：自明 Kan fibration の境界持ち上げの構成。 -/
lemma exists_kanCocartesianSectionsEvaluate_lift {A T E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (a : A ⟶ B) (v : A _⦋0⦌)
    (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v) (U : T.Subcomplex) (g : (U : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a)
    (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (a.app (Opposite.op ⦋0⦌) v))
    (h : g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsEvaluate p a v = U.ι ≫ f) :
    ∃ s : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a,
      U.ι ≫ s = g ∧ s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsEvaluate p a v = f :=
  exists_kanCocartesianSectionsEvaluate_lift_of_fixedPrism p a v
    hv.exists_fixed_initial_prism U g f h

/-- 概要：始対象での cocartesian section の評価は自明 Kan fibration。
方針：任意の標準単体の全境界に対して、指定した評価を保つ相対延長を適用する。
規約：p は cocartesian fibration、底は quasicategory。
使われ方：評価の同値性と、その fiber の可縮性。 -/
lemma cocartesianSectionsEvaluate_trivialKanFibration_of_fixedPrism
    {A E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (a : A ⟶ B) (v : A _⦋0⦌)
    (hC : ∃ C : (Δ[1] : SSet.{u}) ⊗ A ⟶ A,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ C = SSet.const v ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ C = 𝟙 A ∧
      ∀ K : SSet.{u}, (Δ[1] ◁ (SSet.const v : K ⟶ A)) ≫ C = SSet.const v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsEvaluate p a v) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro g f sq
  obtain ⟨s, hsg, hsf⟩ := exists_kanCocartesianSectionsEvaluate_lift_of_fixedPrism
    p a v hC (boundary n) g f sq.w
  exact ⟨⟨s, hsg, hsf⟩⟩

/-- 概要：始対象での cocartesian section の評価は自明 Kan fibration。
方針：任意の標準単体の全境界に対して、指定した評価を保つ相対延長を適用する。
規約：p は cocartesian fibration、底は quasicategory。
使われ方：評価の同値性と、その fiber の可縮性。 -/
@[kerodon 035T]
lemma cocartesianSectionsEvaluate_trivialKanFibration {A E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (a : A ⟶ B) (v : A _⦋0⦌)
    (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsEvaluate p a v) :=
  cocartesianSectionsEvaluate_trivialKanFibration_of_fixedPrism p a v
    hv.exists_fixed_initial_prism

/-- 概要：始対象での cocartesian section の評価は ∞ 圏の同値。
方針：構成済みの自明 Kan fibration による同値判定を使う。
規約：元と標的の quasicategory 性は inner fibration の fiber から得る。
使われ方：strict transport の値と実際の fiber の比較。 -/
lemma cocartesianSectionsEvaluate_isQCatEquivalence {A E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (a : A ⟶ B) (v : A _⦋0⦌)
    (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsEvaluate p a v) := by
  have := cocartesianSectionsEvaluate_trivialKanFibration p a v hv
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.InitialSectionLifting
