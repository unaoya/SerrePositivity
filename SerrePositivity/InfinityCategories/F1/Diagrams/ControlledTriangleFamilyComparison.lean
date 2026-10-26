module

public import SerrePositivity.InfinityCategories.F1.Diagrams.ContractibleFamilyComparison
public import SerrePositivity.InfinityCategories.F1.Diagrams.ControlledTriangleFamilySpaces

/-!
概要：実読出し・再構成の二つの合成を、それぞれ恒等全族へ可逆比較する。
方針：二つの元の可縮 Kan fiber に、全族比較を適用する。
規約：厳密切断や冪等性の等号は結論しない。
使われ方：供給済みの二写像の全パラメーターでの比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (X Z : KanObject.{u}) (K : SSet.{u + 1})
  (c : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
  (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u})
  (encode : controlledTriangleLongHomSpace X Z K c ⟶ controlledTriangleFamilySpace K a)
  (read : controlledTriangleFamilySpace K a ⟶ controlledTriangleLongHomSpace X Z K c)

/-- 読出し後の合成を、L 上の恒等全族へ比較する。 -/
def controlledTriangleFamilyMaps_readEncodeIso : FunctorIso (encode ≫ read) (𝟙 _) :=
  contractibleKanFamilyComparison (controlledTriangleLongHomSpace_isContractibleKan X Z K c) _ _

/-- 再構成後の合成を、同じ固定ホーン T 上の恒等全族へ比較する。 -/
def controlledTriangleFamilyMaps_encodeReadIso : FunctorIso (read ≫ encode) (𝟙 _) :=
  contractibleKanFamilyComparison (controlledTriangleFamilySpace_isContractibleKan K a) _ _

end SerrePositivity.InfinityCategories
