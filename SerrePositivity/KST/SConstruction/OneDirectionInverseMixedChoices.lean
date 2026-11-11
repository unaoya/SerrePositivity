module
public import SerrePositivity.KST.SConstruction.OneDirectionMappingPath
public import SerrePositivity.KST.SConstruction.PointedLiftTransport

/-! # 入力をまたぐ比較逆射の混合選択空間
概要：両端の mapping path 切断の選択を同じ持ち上げ空間へ移す。
方針：mapping path の自然性と持ち上げ空間の全パラメーター移送を使う。
規約：底の入力の射への射影を厳密に固定する。
使われ方：比較逆射の自然性を高次の境界充填で制御する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 入力の射を標的の mapping path へ厳密に持ち上げる混合空間。 -/
def oneDirectionInverseMixedChoices (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) : SSet.{u} :=
  pointedLiftSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app Y))
    ((boundaryKanRealizationFunctor r).map f)

/-- 逆射の混合選択空間は可縮 Kan。 -/
lemma oneDirectionInverseMixedChoices_isContractibleKan (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (oneDirectionInverseMixedChoices r f) :=
  pointedLiftSpace_isContractibleKan _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mappingPathProjection_rlp_of_piIsomorphism _
    (oneDirectionReducedComparison_kan_piIsomorphism r Y)) _

/-- 逆射の混合選択は任意の単射に沿い既存部分を保って補完できる。 -/
lemma oneDirectionInverseMixedChoices_relative_lifting (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    {S T : SSet.{u}} (j : S ⟶ T) [Mono j] (a : S ⟶ oneDirectionInverseMixedChoices r f) :
    ∃ b : T ⟶ oneDirectionInverseMixedChoices r f, j ≫ b = a :=
  pointedLiftSpace_relative_lifting _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mappingPathProjection_rlp_of_piIsomorphism _
    (oneDirectionReducedComparison_kan_piIsomorphism r Y)) _ j a

/-- 源の切断選択を mapping path の入力の射で後合成する。 -/
def oneDirectionInverseMixedFromSource (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    oneDirectionKanInverseChoices r X ⟶ oneDirectionInverseMixedChoices r f :=
  pointedLiftTransport _ _ _ _ (𝟙 _) (oneDirectionMappingPathMap r f)
    ((boundaryKanRealizationFunctor r).map f) (oneDirectionMappingPathMap_projection r f) (by simp)

/-- 標的の切断選択を底の入力の射で前合成する。 -/
def oneDirectionInverseMixedFromTarget (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    oneDirectionKanInverseChoices r Y ⟶ oneDirectionInverseMixedChoices r f :=
  pointedLiftTransport _ _ _ _ ((boundaryKanRealizationFunctor r).map f)
    (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- 混合切断選択から比較逆射の混合写像を取り出す。 -/
def oneDirectionInverseMixedMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (oneDirectionInverseMixedChoices r f) _⦋0⦌) :
    (boundaryKanRealizationFunctor r).obj X ⟶ (oneDirectionKanRealizationFunctor r).obj Y :=
  pointedLiftMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app Y))
    ((boundaryKanRealizationFunctor r).map f) v ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction ((oneDirectionKanComparisonNat r).app Y)

/-- 混合選択の全パラメーターを比較逆射の写像空間へ移す。 -/
def oneDirectionInverseMixedFamily (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    oneDirectionInverseMixedChoices r f ⟶
      (PointedObject.basedHom ((boundaryKanRealizationFunctor r).obj X)
        ((oneDirectionKanRealizationFunctor r).obj Y)).right :=
  pullback.fst
    (PointedObject.basedHomMap ((boundaryKanRealizationFunctor r).obj X)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app Y))).right
    (SSet.yonedaEquiv.symm (familyVertex ((boundaryKanRealizationFunctor r).map f))) ≫
  (PointedObject.basedHomMap ((boundaryKanRealizationFunctor r).obj X)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction ((oneDirectionKanComparisonNat r).app Y))).right

end SerrePositivity.KST.SConstruction
