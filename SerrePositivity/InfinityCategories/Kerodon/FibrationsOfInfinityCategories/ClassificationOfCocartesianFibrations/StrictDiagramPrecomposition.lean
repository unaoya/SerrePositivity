module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportMappingEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementEquivalence

/-!
概要：strict な変換空間の通常の自然変換による前合成。
方針：各対象で通常の射を内部 Hom の単体に前合成し、scaffold 評価と比較する。
規約：前合成の始域図式は共通の通常の圏上に置く。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な図式の同値を写像空間で検出する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：strict な変換を通常の自然変換で前合成する。
方針：各パラメーターで自然変換の成分を先に評価する。
規約：η:F→G により G から H への変換を F から H へ写す。
使われ方：Kerodon §5.3.1（Tag 035D）、strict な変換空間の反変作用。 -/
def strictDiagramMappingPre {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) (H : C ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace G H ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F H where
  app _ := ↾fun θ ↦ ⟨fun c ↦
    Functor.HomObj.comp (Functor.HomObj.ofNatTrans (η.app c)) (θ.val c), by
      intro c d f k α x
      change (H.map f).app k ((θ.val c).app k α ((η.app c).app k x)) =
        (θ.val d).app k α ((η.app d).app k ((F.map f).app k x))
      rw [θ.property]
      exact congrArg ((θ.val d).app k α)
        (congrArg (fun a : F.obj c ⟶ G.obj d ↦ a.app k x) (η.naturality f)).symm⟩
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro θ
    apply Subtype.ext
    funext c
    apply CategoryTheory.Functor.functorHom_ext
    intro k β
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- 概要：strict な変換の前合成は replacement の射による相対前合成と整合する。
方針：scaffold 評価を各単体で計算して、係数への η の作用を比較する。
規約：標的図式は射影 q の strict transport。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、係数ごとの同値を変換空間の同値へ移す可換式。 -/
lemma strictDiagramMappingPre_scaffold {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) {E : SSet.{u}} (q : E ⟶ nerve C) :
    strictDiagramMappingPre η (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldMap F q =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldMap G q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre q
      (Over.homMk (U := Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F))
        (V := Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection G))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementMap η) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementMap_projection η)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
  apply uncurry_injective
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, θ⟩
  rfl

/-- 概要：係数ごとの同値による前合成は strict transport を標的とする変換空間の同値。
方針：scaffold の同型を通じて、replacement の前合成同値の相対 Hom への作用を使う。
規約：始域の二図式は Kan 値、標的 q は left fibration。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict transport の像での同値の判定。 -/
lemma strictDiagramMappingPre_isQCatEquivalence {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)] [∀ c, KanComplex (G.obj c)]
    (η : F ⟶ G) (hη : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (η.app c))
    {E : SSet.{u}} (q : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (strictDiagramMappingPre η (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingScaffoldMap_isQCatEquivalence F q).cancel_right
  rw [strictDiagramMappingPre_scaffold]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingScaffoldMap_isQCatEquivalence G q).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeFunctorOverPre_isQCatEquivalence q
      (Over.homMk (U := Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F))
        (V := Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection G))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementMap η) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementMap_projection η))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementMap_isPrecompositionEquivalence η hη))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
