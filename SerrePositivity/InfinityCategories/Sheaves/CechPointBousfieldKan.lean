module

public import SerrePositivity.InfinityCategories.Sheaves.CechPointElements
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.ReflectedBousfieldKanElements

/-!
概要：既存の Čech 収縮を、元の反転 BK coend とその指定 Kan 置換へ移す。
方針：同じ要素圏への構成済みの同型と、実際の置換の単位の弱同値性を使う。
規約：HTT 4.1.3.1、Kerodon Theorem 7.2.3.1（Tag 02NY）の同じ収縮の模型比較。
使われ方：S8 の各点での余極限比較。元の増大の照合は別の計算則として保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [Category.{v} C] {U V : C}

/-- 同じ Hom 値図式の反転 BK coend は、指定根から弱可縮。 -/
lemma cechPoint_reflectedBousfieldKan_isWeaklyContractible
    (d : CategoryTheory.CechNerveData U) (r : V ⟶ U) :
    IsWeaklyContractible (reflectedBousfieldKanColimit (coefficients (cechPointDiagram d V))) :=
  (isPrecompositionEquivalence_of_iso
    (reflectedBousfieldKanElementsIso (cechPointDiagram d V))).isWeakHomotopyEquivalence.weaklyContractible_iff.mpr
      (cechPointElements_isWeaklyContractible d r)

/-- 元の反転 BK 余極限模型の指定 Kan 置換も、同じ根から弱可縮。 -/
lemma cechPoint_kanReflectedBousfieldKan_isWeaklyContractible
    (d : CategoryTheory.CechNerveData U) (r : V ⟶ U) :
    IsWeaklyContractible
      (kanReflectedBousfieldKanColimitObject (cechPointDiagram d V ⋙ setsToKan)).obj := by
  have hu : IsWeakHomotopyEquivalence
      (anodyneKanObjectUnit (reflectedBousfieldKanColimit
        (coefficients (cechPointDiagram d V)))) := by
    intro Z _
    exact (homotopyEquivalence_pre_of_anodyne _ (anodyneKanObjectUnit_anodyne _) Z).mapPiZero_bijective
  exact hu.weaklyContractible_iff.mp (cechPoint_reflectedBousfieldKan_isWeaklyContractible d r)

end SerrePositivity.InfinityCategories.Sheaves
