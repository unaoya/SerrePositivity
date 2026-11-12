module
public import SerrePositivity.KST.ProExcision.CylinderAWEndpoints

/-!
# 正規化鎖ホモトピーから非被約な実区間ホモトピーへの復元

概要：Dold–Kan で復元した区間射の両端を証明し、実 LinearizedHomotopy に束ねる。
方針：AW の端点計算、Moore 包含の自然性と分裂、正規化の忠実性を合成する。
規約：KST Definition A.3、Construction A.5、被約複体へ移さない。
使われ方：正規化した augmentation 補正式の鎖ホモトピーを実単体的区間へ戻す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
variable {X : SSet.{u}} {D : SimplicialObject (ModuleCat.{u} ℤ)}
variable {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ D}
variable (H : Homotopy ((normalizedMooreComplex _).map f) ((normalizedMooreComplex _).map g))

/-- 概要：構成した正規化区間の鎖写像の始点は指定した始点写像。
方針：Moore 包含の自然性と AW の端点計算の後、包含・射影の分裂を使う。
規約：KST A.3・A.5。使われ方：復元した実区間射の始点の検証。 -/
lemma chainHomotopyCylinderMap_endpoint₀ :
    (normalizedMooreComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀ X) ≫ chainHomotopyCylinderMap H =
      (normalizedMooreComplex _).map f := by
  have hi := (inclusionOfMooreComplex (ModuleCat.{u} ℤ)).naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀ X)
  change (normalizedMooreComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀ X) ≫
    inclusionOfMooreComplexMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinder X) =
      inclusionOfMooreComplexMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) ≫
        (alternatingFaceMapComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀ X) at hi
  have hs : inclusionOfMooreComplexMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) ≫
      PInftyToNormalizedMooreComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) = 𝟙 _ :=
    (splitMonoInclusionOfMooreComplexMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X)).id
  rw [chainHomotopyCylinderMap, ← Category.assoc, hi, Category.assoc,
    chainHomotopyCylinderCore_endpoint₀, ← Category.assoc, hs, Category.id_comp]

/-- 概要：構成した正規化区間の鎖写像の終点は指定した終点写像。
方針：Moore 包含の自然性と AW の端点計算の後、包含・射影の分裂を使う。
規約：KST A.3・A.5。使われ方：復元した実区間射の終点の検証。 -/
lemma chainHomotopyCylinderMap_endpoint₁ :
    (normalizedMooreComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁ X) ≫ chainHomotopyCylinderMap H =
      (normalizedMooreComplex _).map g := by
  have hi := (inclusionOfMooreComplex (ModuleCat.{u} ℤ)).naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁ X)
  change (normalizedMooreComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁ X) ≫
    inclusionOfMooreComplexMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinder X) =
      inclusionOfMooreComplexMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) ≫
        (alternatingFaceMapComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁ X) at hi
  have hs : inclusionOfMooreComplexMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) ≫
      PInftyToNormalizedMooreComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) = 𝟙 _ :=
    (splitMonoInclusionOfMooreComplexMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X)).id
  rw [chainHomotopyCylinderMap, ← Category.assoc, hi, Category.assoc,
    chainHomotopyCylinderCore_endpoint₁, ← Category.assoc, hs, Category.id_comp]

/-- 概要：復元した実単体的区間射の始点は指定した実射。
方針：正規化後の始点の等式を忠実性で実射へ戻す。
規約：KST A.3・A.5。使われ方：LinearizedHomotopy の始点条件。 -/
lemma chainHomotopyCylinderReconstruct_endpoint₀ :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀ X ≫ chainHomotopyCylinderReconstruct H = f := by
  apply normalizedMap_eq_of_map_eq
  rw [CategoryTheory.Functor.map_comp, chainHomotopyCylinderReconstruct_map,
    chainHomotopyCylinderMap_endpoint₀]

/-- 概要：復元した実単体的区間射の終点は指定した実射。
方針：正規化後の終点の等式を忠実性で実射へ戻す。
規約：KST A.3・A.5。使われ方：LinearizedHomotopy の終点条件。 -/
lemma chainHomotopyCylinderReconstruct_endpoint₁ :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁ X ≫ chainHomotopyCylinderReconstruct H = g := by
  apply normalizedMap_eq_of_map_eq
  rw [CategoryTheory.Functor.map_comp, chainHomotopyCylinderReconstruct_map,
    chainHomotopyCylinderMap_endpoint₁]

/-- 概要：正規化鎖ホモトピーを非被約な実単体的区間ホモトピーへ復元する。
方針：AW・鎖区間比較・評価・Dold–Kan の実復元に両端の証明を付ける。
規約：KST Definition A.3、Construction A.5、復元の存在を追加仮定にしない。
使われ方：正規化した差のテンソルの低次消滅を C(H) の実区間へ戻す。 -/
def LinearizedHomotopy.ofNormalizedChainHomotopy : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedHomotopy f g where
  h := chainHomotopyCylinderReconstruct H
  h₀ := chainHomotopyCylinderReconstruct_endpoint₀ H
  h₁ := chainHomotopyCylinderReconstruct_endpoint₁ H

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedHomotopy export _root_.SerrePositivity.KST.ProExcision.LinearizedHomotopy (ofNormalizedChainHomotopy)

end SerrePositivity.KST.ProExcision
