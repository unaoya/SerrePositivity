module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinDiagonalOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePrisms

/-!
概要：写像空間の左右の円柱比較は反転で交換される。
方針：両円柱を join の対角の一因子を点に潰す射とし、対角の反転を適用する。
規約：区間の時間も反転し、点の反転同型を明示する。
使われ方：slice の標準指定変換と反転した coslice の変換を比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams

/-- 概要：右の点付き円柱は対角の右因子を点に潰した射。
方針：円柱比較の自然性を使い、円柱への入力を成分ごとに計算する。
規約：空の A も含む。
使われ方：点付き円柱の反転を対角の反転に帰着する。 -/
lemma joinDiagonal_rightPoint (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) (SSet.const (stdSimplex.obj₀Equiv.symm 0) : A ⟶ Δ[0]) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism A := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_naturality]
  rfl

/-- 概要：左の点付き円柱は対角の左因子を点に潰した射。
方針：円柱比較の自然性と入力の二つの射影を使う。
規約：点は標準零単体の唯一の頂点。
使われ方：反転後の点付き円柱を認識する。 -/
lemma joinDiagonal_leftPoint (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.const (stdSimplex.obj₀Equiv.symm 0) : A ⟶ Δ[0]) (𝟙 A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingSpacePrism A := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_naturality]
  rfl

/-- 概要：右の円柱比較の反転は左の円柱比較に点の反転同型を前合成したもの。
方針：対角の反転と join の反転の自然性を組み合わせる。
規約：Δ⁰.op と Δ⁰ を定義的に同一視しない。
使われ方：標準の局所指定変換を反転から戻す。 -/
lemma rightMappingSpacePrism_reverse (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism A) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso A Δ[0]).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingSpacePrism A.op ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 A.op) := by
  rw [← joinDiagonal_rightPoint, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_postcomp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverse_naturality, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinDiagonal_reverse]
  have hp : SSet.opFunctor.map (SSet.const (stdSimplex.obj₀Equiv.symm 0) : A ⟶ Δ[0]) =
      (SSet.const (stdSimplex.obj₀Equiv.symm 0) : A.op ⟶ Δ[0]) ≫
        (stdSimplex.opIso ⦋0⦌).inv := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    apply (SSet.opObjEquiv (X := (Δ[0] : SSet.{u}))).injective
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    omega
  rw [hp, ← joinDiagonal_leftPoint, CategoryTheory.Functor.map_id]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp (SSet.const (stdSimplex.obj₀Equiv.symm 0) : A.op ⟶ Δ[0])
    (stdSimplex.opIso ⦋0⦌).inv (𝟙 A.op) (𝟙 A.op)
  simp only [Category.id_comp] at h
  rw [h, Category.assoc]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams
