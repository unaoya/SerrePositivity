module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveTensor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramSimplicialCategory
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveLeftFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition

/-!
概要：weighted nerve の strict な変換空間の全次数への作用。
方針：変換の全空間を係数のパラメーターへ移して評価し、底上の族を相対 curry する。
規約：作用は単位と合成を厳密に保つ。
使われ方：Kerodon §§5.3.3（Tag 025W）、5.6.5（Tag 028U）、strict な比較の族から left fibrations の coherent な族を構成する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：strict な変換空間の全体で weighted nerve を評価する。
方針：変換のパラメーターを係数へ移し、係数の普遍的な評価を weighted nerve に作用させる。
規約：入力図式には Kan 性を要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、weighted nerve の豊穣作用の相対 uncurry。 -/
def weightedNerveMappingFamily {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTensorMap F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingEvaluation F G)

/-- 概要：変換空間での weighted nerve の評価は元の底を保つ。
方針：係数の評価とパラメーター移送の二つの射影の計算を合成する。
規約：底への射影では変換のパラメーターを忘れる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対写像空間に持ち上げる条件。 -/
lemma weightedNerveMappingFamily_projection {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    weightedNerveMappingFamily F G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection G =
      CartesianMonoidalCategory.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F := by
  rw [weightedNerveMappingFamily, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap_projection,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTensorMap_projection]

/-- 概要：strict な変換空間を weighted nerves 間の相対写像空間へ写す。
方針：底を保つ全変換の評価を相対 curry する。
規約：全次数の単体集合の射であり、頂点だけの作用ではない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、weighted nerve を豊穣関手として扱う Hom の作用。 -/
def weightedNerveMappingSpaceMap {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection G) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry (weightedNerveMappingFamily F G) (weightedNerveMappingFamily_projection F G)

/-- 概要：weighted nerve の Hom の作用を相対展開すると全変換の評価を回収する。
方針：相対 curry と uncurry の往復を使う。
規約：構成した底上の族そのものとの厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、単位・合成と自然な比較の計算の出発点。 -/
lemma weightedNerveMappingSpaceMap_uncurry {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (weightedNerveMappingSpaceMap F G) = weightedNerveMappingFamily F G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry _ _

/-- 概要：weighted nerve の全次数の Hom の作用は豊穣単位を保つ。
方針：相対展開後に各係数の初区間の単体で恒等変換を評価する。
規約：入力図式の Kan 性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、weighted nerve の豊穣関手の単位則。 -/
lemma weightedNerveMappingSpaceMap_identity {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingIdentity F ≫ weightedNerveMappingSpaceMap F F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity (Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext i
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 概要：weighted nerve の全次数の Hom の作用は豊穣合成を保つ。
方針：相対展開後に、同じ初区間に制限した二つの変換を順に評価する。
規約：単体の全パラメーターを保持した射の等式。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、weighted nerve の豊穣関手の合成則。 -/
lemma weightedNerveMappingSpaceMap_composition {C : Type u} [Category.{u} C]
    (F G H : C ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingComposition F G H ≫ weightedNerveMappingSpaceMap F H =
      (weightedNerveMappingSpaceMap F G ⊗ₘ weightedNerveMappingSpaceMap G H) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition (Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F))
          (Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection G)) (Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, η, θ⟩
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext i
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 概要：weighted nerve は strict Kan 図式の単体的圏から left fibrations の単体的圏への豊穣関手。
方針：対象には weighted nerve の射影を、Hom には全変換の相対評価を使う。
規約：始域の変換空間が Kan であるとは仮定しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な比較の全高次パラメーターを保持した復元。 -/
def weightedNerveKanEnriched (C : Type u) [Category.{u} C] :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject C) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject (nerve C)) where
  obj F := ⟨Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)), by
    have : ∀ c, KanComplex ((F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).obj c) := fun c ↦ (F.val.obj c).isKanComplex
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection_leftFibration (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)⟩
  map F G := weightedNerveMappingSpaceMap (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
  map_id F := weightedNerveMappingSpaceMap_identity _
  map_comp F G H := weightedNerveMappingSpaceMap_composition _ _ _

/-- 概要：strict Kan 図式の coherent な族を、weighted nerve による left fibrations の coherent な族へ写す。
方針：構成した豊穣関手に coherent nerve を適用する。
規約：この写像の同値性や一般の coherent 図式の分類はここでは主張しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、straightening の strict な像との全次数での比較。 -/
noncomputable def weightedNerveInfinityMap (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNerve C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity (nerve C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (weightedNerveKanEnriched C)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
