module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTotalCoconePre
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeFiberColimitCriterion

/-!
概要：小さい底上の任意の coherent 空間値図式の全空間 Kan 模型が元の余錐の native な余極限。
方針：元の単位比較による全 fiber 標的への前合成同値を元の全 Hom の判定へ入力する。
規約：元の図式と構成済みの余錐を保持し、filtered 性を要求しない。
使われ方：一般 coherent filtered 余極限と有限極限の交換、Ind の生成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}

/-- 概要：構成済み全空間余錐そのものが元の coherent 図式の native な余極限。
方針：元の単位から証明した全 fiber 前合成同値に、元の全 Hom の余極限判定を適用する。
規約：図式・余錐を選び直さない。使われ方：全空間 Kan 模型の普遍性。 -/
lemma coherentDiagramTotalCocone_isColimit
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    IsColimitCone (coherentDiagramTotalCocone F) :=
  isColimitCone_of_coconeFiberMap_pre_homotopyEquivalence (coherentDiagramTotalCocone F)
    (coherentTotalCoconeFiber_pre_homotopyEquivalence F)

/-- 概要：小さい底上の任意の coherent 空間値図式は native な余極限を持つ。
方針：元の全空間余錐とその証明済みの普遍性を供給する。
規約：strict 図式への置換を仮定しない。使われ方：一般 coherent 余極限の存在。 -/
lemma hasColimit_coherentSpaceDiagram
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) : HasColimit F :=
  ⟨coherentDiagramTotalCocone F, coherentDiagramTotalCocone_isColimit F⟩

end SerrePositivity.InfinityCategories.F2
