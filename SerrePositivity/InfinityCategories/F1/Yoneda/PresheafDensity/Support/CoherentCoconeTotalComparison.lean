module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeTransformationEquivalence
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoherentSmallConstantTarget

/-!
概要：一般 coherent 空間値図式の native な余錐空間を、小さい全空間からの写像空間へ比較する。
方針：native 余錐から定値変換への標準同値と、F1 の unstraightening 比較を合成する。
規約：元の図式は任意で、filtered 性や strict 図式の仮定は不要。
使われ方：全空間 Kan 模型の native な余極限性を全 Hom の族で検査する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}

/-- 概要：元の図式の native 余錐空間から小さい全空間の内部 Hom の持ち上げへの比較。
方針：全パラメータを保持する二つの実際の比較射を続ける。
規約：標的は元の頂点が表す Kan 値。使われ方：全 Hom の余極限判定の共通模型。 -/
def coherentCoconeTotalComparison
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (z : SpaceInfinity.{u} _⦋0⦌) :
    coconeMappingSpace F z ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
      ((ihom (smallLeftUnstraightening F)).obj (spaceInfinityObject z).obj) :=
  coconeTransformationMap F z ≫ coherentSmallConstantTargetMap F z

/-- 概要：native な余錐空間と元の小さい全空間からの写像空間の標準比較は圏同値。
方針：二つの標準比較の同値性を合成する。
規約：任意の coherent 図式と任意の頂点。使われ方：native 余極限性への反映。 -/
lemma coherentCoconeTotalComparison_isQCatEquivalence
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (z : SpaceInfinity.{u} _⦋0⦌) : IsQCatEquivalence (coherentCoconeTotalComparison F z) :=
  (coconeTransformationMap_isQCatEquivalence F z).comp
    (coherentSmallConstantTargetMap_isQCatEquivalence F z)

/-- 概要：native な余錐空間の全空間比較は実際のホモトピー逆を持つ。
方針：両模型の Kan 性と同値性を使う。
規約：全ての高次パラメータを含む。使われ方：全 Hom による判定への直接入力。 -/
lemma coherentCoconeTotalComparison_homotopyEquivalence
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (z : SpaceInfinity.{u} _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (coherentCoconeTotalComparison F z) :=
  (coherentCoconeTotalComparison_isQCatEquivalence F z).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2
