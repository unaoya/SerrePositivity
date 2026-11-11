module
public import SerrePositivity.KST.SConstruction.PointedMappingCompositionFamilies
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.ContractibleKanProducts
public import SerrePositivity.KST.SConstruction.OneDirectionInverseChoices
public import SerrePositivity.KST.SConstruction.KanAssemblyEquivalence

/-! # 境界商の随伴構造射の同時選択とパラメーター族
概要：比較逆射と Kan 延長の全選択を合成する実際の写像空間の族を構成する。
方針：可縮な二つの選択空間の積と点つき写像空間の豊穣合成を使う。
規約：各頂点で既存の随伴構造射との点つきホモトピー比較を保持する。
使われ方：構造射の coherent な自然性を列の厳密化へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory SSet
open Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- Kan 延長の全選択を元の点つき写像空間へ移す族。 -/
def kanAssemblyAdjointFamily (r : ℕ) (X : StableModel.{u}) :
    kanAssemblyAdjointChoices r X ⟶
      (PointedObject.basedHom ((oneDirectionKanRealizationFunctor r).obj X)
        ((loopBoundaryKanFunctor (r + 1)).obj X)).right :=
  pullback.fst
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedKanReplacement.unit.app (oneDirectionReducedRealization r X))
      ((loopBoundaryKanFunctor (r + 1)).obj X)).right
    (SSet.yonedaEquiv.symm (familyVertex ((kanTargetAssemblyAdjointNat r).app X)))

/-- Kan 延長の族は各頂点で同じ選択の実際の射を回収する。 -/
lemma kanAssemblyAdjointFamily_vertex (r : ℕ) (X : StableModel.{u})
    (v : (kanAssemblyAdjointChoices r X) _⦋0⦌) :
    (kanAssemblyAdjointFamily r X).app (Opposite.op ⦋0⦌) v =
      familyVertex (kanAssemblyAdjointAt r X v) :=
  (familyVertex_familyMap _ _ _).symm

/-- 比較逆射と Kan 延長を同時に選ぶ空間。 -/
def boundaryKanAssemblyChoices (r : ℕ) (X : StableModel.{u}) : SSet.{u} :=
  oneDirectionKanInverseChoices r X ⊗ kanAssemblyAdjointChoices r X

/-- 随伴構造射の同時選択空間は可縮 Kan。 -/
lemma boundaryKanAssemblyChoices_isContractibleKan (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (boundaryKanAssemblyChoices r X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.contractibleKan_tensor (oneDirectionKanInverseChoices_isContractibleKan r X)
    (kanAssemblyAdjointChoices_isContractibleKan r X)

/-- 同時選択のパラメーター族を既存部分を保って任意の単射に沿い補完できる。 -/
lemma boundaryKanAssemblyChoices_relative_lifting (r : ℕ) (X : StableModel.{u})
    {S T : SSet.{u}} (j : S ⟶ T) [Mono j] (a : S ⟶ boundaryKanAssemblyChoices r X) :
    ∃ b : T ⟶ boundaryKanAssemblyChoices r X, j ≫ b = a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.contractibleKan_tensor_relative_lifting (oneDirectionKanInverseChoices_isContractibleKan r X)
    (kanAssemblyAdjointChoices_isContractibleKan r X) j a

/-- 同時選択頂点が与える実際の随伴構造射。 -/
def boundaryKanAssemblyAdjointAt (r : ℕ) (X : StableModel.{u})
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌) :
    (boundaryKanRealizationFunctor r).obj X ⟶ (loopBoundaryKanFunctor (r + 1)).obj X :=
  oneDirectionKanInverseAt r X v.1 ≫ kanAssemblyAdjointAt r X v.2

/-- 逆射と延長を全パラメーターで同時に合成する随伴構造射の族。 -/
def boundaryKanAssemblyAdjointFamily (r : ℕ) (X : StableModel.{u}) :
    boundaryKanAssemblyChoices r X ⟶
      (PointedObject.basedHom ((boundaryKanRealizationFunctor r).obj X)
        ((loopBoundaryKanFunctor (r + 1)).obj X)).right :=
  (pointedMappingPathInverseFamily ((oneDirectionKanComparisonNat r).app X) ⊗ₘ
    kanAssemblyAdjointFamily r X) ≫ pointedMappingComposition _ _ _

/-- 構造射の族は各同時選択頂点で実際の随伴射を回収する。 -/
lemma boundaryKanAssemblyAdjointFamily_vertex (r : ℕ) (X : StableModel.{u})
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌) :
    (boundaryKanAssemblyAdjointFamily r X).app (Opposite.op ⦋0⦌) v =
      familyVertex (boundaryKanAssemblyAdjointAt r X v) := by
  change (pointedMappingComposition _ _ _).app (Opposite.op ⦋0⦌)
    ((pointedMappingPathInverseFamily _).app _ v.1, (kanAssemblyAdjointFamily r X).app _ v.2) = _
  rw [pointedMappingPathInverseFamily_vertex, kanAssemblyAdjointFamily_vertex,
    pointedMappingComposition_vertex]
  rfl

/-- 元の随伴構造射と任意の同時選択の随伴射は同じ点つきホモトピー成分。 -/
lemma boundaryKanAssemblyAdjointAt_component (r : ℕ) (X : StableModel.{u})
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌) :
    componentOf (boundaryKanAssemblyAdjoint r X) = componentOf (boundaryKanAssemblyAdjointAt r X v) := by
  let w := (kanAssemblyAdjointChoices_isContractibleKan r X).nonempty.some
  have hi := componentOf_comp_right (oneDirectionKanInverseAt_component r X v.1)
    (kanAssemblyAdjointAt r X w)
  have hk := componentOf_comp_left
    ((piZero_eq_iff_pointedHomotopy _ _).mpr (kanAssemblyAdjointAt_homotopy r X w v.2))
    (oneDirectionKanInverseAt r X v.1)
  exact hi.trans hk

/-- 任意の同時選択の随伴構造射も全基点 π 同型。 -/
lemma boundaryKanAssemblyAdjointAt_piIsomorphism (r : ℕ) (X : StableModel.{u})
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (boundaryKanAssemblyAdjointAt r X v).right := by
  obtain ⟨H, _⟩ := (piZero_eq_iff_pointedHomotopy _ _).mp
    (boundaryKanAssemblyAdjointAt_component r X v)
  exact (kanPiIsomorphism_iff_of_homotopy H).mp (boundaryKanAssemblyAdjoint_piIsomorphism r X)

end SerrePositivity.KST.SConstruction
