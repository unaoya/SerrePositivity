module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessDescentLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan

/-!
概要：底上の非交和の表現空間を各項の表現空間の積と同定する。
方針：反対圏の非交和と積の同型および極限保存を用いる。
規約：全高次単体の同型であり各項への制限を保持する。
使われ方：零次骨格とセル族の表現空間の可縮性。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：底上の非交和の表現空間は表現空間の積と厳密に同型。
方針：反対圏の標準同型を写し、積の保存同型を続ける。
規約：添字は単体集合の宇宙で小さい。
使われ方：セル族と零次骨格の表現の同時選択。 -/
def transportWitnessCoproductIso {E B : SSet.{u + 1}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    {I : Type (u + 1)} (a : I → Over B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj (Opposite.op (∐ a)) ≅
      ∏ᶜ (fun i ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj (Opposite.op (a i))) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).mapIso (opCoproductIsoProduct a) ≪≫
    PreservesProduct.iso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p) (fun i ↦ Opposite.op (a i))

/-- 概要：非交和の表現空間の積比較は各項への実際の制限を回収する。
方針：積の比較射と反対圏の標準同型の射影公式を使う。
規約：全次数の射の等式。
使われ方：貼り合わせた表現の各セルへの制限。 -/
lemma transportWitnessCoproductIso_hom_π {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {I : Type (u + 1)} (a : I → Over B) (i : I) :
    (transportWitnessCoproductIso p a).hom ≫ Pi.π _ i =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).map (Sigma.ι a i).op := by
  dsimp only [transportWitnessCoproductIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π,
    ← Functor.map_comp, opCoproductIsoProduct_hom_comp_π]

/-- 概要：可縮 Kan 複体の小さい積は可縮 Kan。
方針：境界の各成分を充填し積の普遍性で束ねる。
規約：空の積も含み、非空性の仮定は不要。
使われ方：非交和の表現空間の可縮性。 -/
lemma isContractibleKan_pi {I : Type (u + 1)} (K : I → SSet.{u + 1})
    (h : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (K i)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (∏ᶜ K) := by
  intro n b
  choose F hF using fun i ↦ h i n (b ≫ Pi.π K i)
  refine ⟨Pi.lift F, ?_⟩
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, Pi.lift_comp_π, hF]

/-- 概要：各項の表現空間が可縮なら非交和上の表現空間も可縮。
方針：積の可縮性を非交和の厳密な比較同型で移す。
規約：空の族を含む。
使われ方：零次骨格とセル族の可縮性の入力。 -/
lemma transportWitnessCoproduct_isContractibleKan {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {I : Type (u + 1)} (a : I → Over B)
    (h : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj (Opposite.op (a i)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj (Opposite.op (∐ a))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso (transportWitnessCoproductIso p a).symm
    (isContractibleKan_pi _ h)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
