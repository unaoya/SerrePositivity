module

public import SerrePositivity.InfinityCategories.F2.CoconeTransformationRetraction
public import SerrePositivity.InfinityCategories.F2.CoconeTransformationRightInverse
public import SerrePositivity.InfinityCategories.F1.EquivalenceRetraction
public import SerrePositivity.InfinityCategories.F1.PreFiberKan

/-!
概要：native な終点固定余錐空間と定値図式への変換空間の標準比較は同値。
方針：厳密な左逆と全パラメータのホモトピー右逆を同じ比較射に対して組み合わせる。
規約：任意の形状と quasicategory 標的。filtered 性や strict 図式を仮定しない。
使われ方：一般 coherent 図式の余極限を全 Hom で判定する共通模型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：native な余錐から定値標的への変換への実際の標準比較は圏同値。
方針：厳密な左逆と恒等族の回収によるホモトピー右逆を合わせる。
規約：元の比較射そのものに対する判定。使われ方：余錐空間の共通表示。 -/
lemma coconeTransformationMap_isQCatEquivalence {K X : SSet.{u}} [Quasicategory X]
    (f : K ⟶ X) (z : X _⦋0⦌) : IsQCatEquivalence (coconeTransformationMap f z) := by
  obtain ⟨r, hr⟩ := coconeTransformationMap_exists_retraction f z
  obtain ⟨b, ⟨H⟩⟩ := coconeTransformationMap_exists_homotopy
    (𝟙 (intervalMappingSpace (functorVertex f) (functorVertex (SSet.const z))))
  exact isQCatEquivalence_of_retraction_of_rightInverseIso _ r b hr
    (functorIsoOfSimplicialHomotopy H)

/-- 概要：native な余錐空間の標準比較は実際のホモトピー逆を持つ。
方針：両空間の Kan 性と圏同値性の判定を使う。
規約：全ての高次パラメータを含む。使われ方：全 Hom による余極限判定への入力。 -/
lemma coconeTransformationMap_homotopyEquivalence {K X : SSet.{u}} [Quasicategory X]
    (f : K ⟶ X) (z : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (coconeTransformationMap f z) :=
  (coconeTransformationMap_isQCatEquivalence f z).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2
