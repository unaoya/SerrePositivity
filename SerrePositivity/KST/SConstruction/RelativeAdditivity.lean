module
public import SerrePositivity.KST.SConstruction.RelativeFiberEquivalence
public import SerrePositivity.KST.SConstruction.CoreAdditivity

/-! # E(A,C,B) の相対加法性
概要：相対 cofiber 図式の subobject・quotient は object S と core S の実現後に積への弱同値。
方針：相対左 fiber 内で証明した二ホモトピーを単体積版 Quillen A に渡し、自然な object/core 比較で移す。
規約：全 cofiber 図式の弱同値の部分圏への制限からは結論しない。
使われ方：Fiore–Pieper の相対加法性と fibration 定理。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel

/-- E(A,C,B) の元の subobject・quotient の object S の射対。 -/
def relativeObjectSAdditivityMap {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    objectSConstruction (relativeCofiberDiagrams A B) ⟶
      objectSConstruction (closedSubcategory A) ⊗ objectSConstruction (closedSubcategory B) :=
  CartesianMonoidalCategory.lift
    (objectSConstructionFunctor.map (relativeCofiberSubobject A B))
    (objectSConstructionFunctor.map (relativeCofiberQuotient A B))

/-- 相対 object S 加法性：元の射対は anodyne 局所化で同型。 -/
lemma relativeObjectSAdditivityMap_localized_isIso {X : StableModel.{u}}
    (A B : ClosedStablePredicate X) :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeObjectSAdditivityMap A B)) :=
  simplicialProductQuillenA
    (objectSConstructionFunctor.map (relativeCofiberSubobject A B))
    (objectSConstructionFunctor.map (relativeCofiberQuotient A B))
    (fun _ a => relativeCofiberLeftFiberQuotient_localized_isIso A B a)

/-- 二つの異なる安定な入力の object/core 比較の積も局所化同型。 -/
lemma objectCoreComparisons_tensor_localized_isIso (X Y : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (objectToCoreSRealization X.carrier ⊗ₘ objectToCoreSRealization Y.carrier)) := by
  have hX := objectToCoreSRealization_localized_isIso X.carrier
  have hY := objectToCoreSRealization_localized_isIso Y.carrier
  have := AnodyneHomotopy.whiskerRight_anodyneQ_isIso
    (objectToCoreSRealization X.carrier) hX (objectSConstruction Y.carrier)
  have := AnodyneHomotopy.whiskerLeft_anodyneQ_isIso
    (objectToCoreSRealization Y.carrier) hY
      (simplicialDiagonalFunctor.obj (simplicialCoreSConstruction X.carrier))
  rw [tensorHom_def, AnodyneHomotopy.anodyneQ.map_comp]
  infer_instance

/-- 相対 cofiber 図式の元の二つの完全な評価の core S• 実現の射対。 -/
def relativeCoreSAdditivityMap {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    coreSRealizationFunctor.obj (relativeCofiberStableModel A B) ⟶
      coreSRealizationFunctor.obj (closedStableModel A) ⊗
        coreSRealizationFunctor.obj (closedStableModel B) :=
  CartesianMonoidalCategory.lift
    (coreSRealizationFunctor.map (relativeCofiberSubobject A B))
    (coreSRealizationFunctor.map (relativeCofiberQuotient A B))

/-- 相対加法性の正方形は元の object/core 比較で厳密に可換。 -/
lemma relativeObjectCoreAdditivity_commute {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    relativeObjectSAdditivityMap A B ≫
      (objectToCoreSRealization (closedSubcategory A) ⊗ₘ
        objectToCoreSRealization (closedSubcategory B)) =
    objectToCoreSRealization (relativeCofiberDiagrams A B) ≫ relativeCoreSAdditivityMap A B := by
  change CartesianMonoidalCategory.lift
      (objectSConstructionFunctor.map (relativeCofiberSubobject A B))
      (objectSConstructionFunctor.map (relativeCofiberQuotient A B)) ≫
        (objectCoreRealizationComparison.app (closedStableModel A) ⊗ₘ
          objectCoreRealizationComparison.app (closedStableModel B)) =
    objectCoreRealizationComparison.app (relativeCofiberStableModel A B) ≫
      CartesianMonoidalCategory.lift
        (coreSRealizationFunctor.map (relativeCofiberSubobject A B))
        (coreSRealizationFunctor.map (relativeCofiberQuotient A B))
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_fst,
      CartesianMonoidalCategory.lift_fst_assoc, CartesianMonoidalCategory.lift_fst]
    exact objectCoreRealizationComparison.naturality (relativeCofiberSubobject A B)
  · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_snd,
      CartesianMonoidalCategory.lift_snd_assoc, CartesianMonoidalCategory.lift_snd]
    exact objectCoreRealizationComparison.naturality (relativeCofiberQuotient A B)

/-- 相対 core S• 実現の加法性：元の射対は anodyne 局所化で同型。 -/
lemma relativeCoreSAdditivityMap_localized_isIso {X : StableModel.{u}}
    (A B : ClosedStablePredicate X) :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeCoreSAdditivityMap A B)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have : IsIso (Q.map (relativeObjectSAdditivityMap A B)) :=
    relativeObjectSAdditivityMap_localized_isIso A B
  have : IsIso (Q.map (objectToCoreSRealization (closedSubcategory A) ⊗ₘ
      objectToCoreSRealization (closedSubcategory B))) :=
    objectCoreComparisons_tensor_localized_isIso (closedStableModel A) (closedStableModel B)
  have : IsIso (Q.map (objectToCoreSRealization (relativeCofiberDiagrams A B))) :=
    objectToCoreSRealization_localized_isIso (relativeCofiberDiagrams A B)
  have he := congrArg Q.map (relativeObjectCoreAdditivity_commute A B)
  rw [Q.map_comp, Q.map_comp] at he
  have hi : IsIso (Q.map (objectToCoreSRealization (relativeCofiberDiagrams A B)) ≫
      Q.map (relativeCoreSAdditivityMap A B)) := he ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp hi

end SerrePositivity.KST.SConstruction
