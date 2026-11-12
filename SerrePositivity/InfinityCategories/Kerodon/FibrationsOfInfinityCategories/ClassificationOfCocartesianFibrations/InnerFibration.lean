module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseLeftFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Kan

/-!
概要：宇宙持ち上げによる inner fibration 性と quasicategory 性の保存。
方針：既存のホーンの相対持ち上げの宇宙移送を内ホーンに適用する。
規約：モデル構造を使わず、ホーン充填条件だけを移す。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict transport の全空間比較の宇宙を揃える。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：inner fibration の射を宇宙持ち上げしても inner fibration。
方針：各内ホーンの相対持ち上げを元の宇宙に戻し、充填を持ち上げる。
規約：追加の宇宙 v は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、底上の共通の比較空間の持ち上げ。 -/
instance innerFibration_uliftFunctor_map {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p] :
    InnerFibration ((SSet.uliftFunctor.{v, u}).map p) := by
  constructor
  intro X Y i hi
  obtain @⟨n, i, h0, hn⟩ := hi
  have : HasLiftingProperty (horn.{u} (n + 2) i).ι p :=
    (InnerFibration.mem (q := p)) _ (innerHornInclusions.intro i h0 hn)
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ulift_hasLiftingProperty_horn p (n + 1) i

/-- 概要：quasicategory の単体を宇宙持ち上げしても quasicategory。
方針：終対象への inner fibration を持ち上げ、その標的の Kan 性を使う。
規約：単体集合のサイズだけを変更する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、𝒮 と同じ宇宙での全空間の同値比較。 -/
instance quasicategory_uliftFunctor_obj (E : SSet.{u}) [Quasicategory E] :
    Quasicategory ((SSet.uliftFunctor.{v, u}).obj E) := by
  have : KanComplex (Δ[0] : SSet.{u}) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.isKanComplex
  have : KanComplex (⊤_ SSet.{u}) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso
    (stdSimplex.isTerminalObj₀.uniqueUpToIso terminalIsTerminal)
  exact quasicategory_of_innerFibration ((SSet.uliftFunctor.{v, u}).map (terminal.from E))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
