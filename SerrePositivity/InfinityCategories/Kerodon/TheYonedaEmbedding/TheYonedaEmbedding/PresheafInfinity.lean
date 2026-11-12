module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PreFiberKan
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation

/-!
概要：小さい単体集合上の空間値前層の ∞ 圏と、その制限・評価を構成する。
方針：反転した底を値の宇宙へ持ち上げ、空間の ∞ 圏への内部 Hom を取る。
規約：小さい底と空間の宇宙を明示し、分類同値や Yoneda の充満忠実性を仮定しない。
使われ方：F1-2 の前層 ∞ 圏と、Yoneda 埋め込みの値域。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 小さい底 C 上の空間値前層の ∞ 圏 Fun(Cᵒᵖ, 𝒮)。 -/
def PresheafInfinity (C : SSet.{u}) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj C.op)

/-- 前層の関手単体集合は、底に充填条件を課さず quasicategory となる。 -/
instance presheafInfinity_quasicategory (C : SSet.{u}) : Quasicategory (PresheafInfinity C) :=
  inferInstanceAs (Quasicategory
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj C.op)))

/-- 底の射 f : C → D に沿う前層の制限 f* : P(D) → P(C)。 -/
def presheafInfinityRestriction {C D : SSet.{u}} (f : C ⟶ D) :
    PresheafInfinity D ⟶ PresheafInfinity C :=
  (pre ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map f))).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}

/-- 恒等写像への制限は前層 ∞ 圏の恒等射。 -/
lemma presheafInfinityRestriction_id (C : SSet.{u}) :
    presheafInfinityRestriction (𝟙 C) = 𝟙 (PresheafInfinity C) := by
  have h : (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map (𝟙 C)) =
      𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj C.op) :=
    (congrArg (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map_id C)).trans
      ((SSet.uliftFunctor.{u + 1, u}).map_id C.op)
  rw [presheafInfinityRestriction, h, pre_id]
  rfl

/-- 前層の制限は、底の合成を逆順の合成へ厳密に写す。 -/
lemma presheafInfinityRestriction_comp {C D E : SSet.{u}} (f : C ⟶ D) (g : D ⟶ E) :
    presheafInfinityRestriction (f ≫ g) =
      presheafInfinityRestriction g ≫ presheafInfinityRestriction f := by
  simp only [presheafInfinityRestriction, Functor.map_comp, pre_map, NatTrans.comp_app]

/-- 前層を底の指定頂点で評価する ∞ 関手。 -/
def presheafInfinityEvaluation {C : SSet.{u}} (c : C _⦋0⦌) :
    PresheafInfinity C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm c))

/-- 制限した前層の頂点評価は、像の頂点で元の前層を評価する射そのもの。 -/
lemma presheafInfinityRestriction_evaluation {C D : SSet.{u}} (f : C ⟶ D)
    (c : C _⦋0⦌) :
    presheafInfinityRestriction f ≫ presheafInfinityEvaluation c =
      presheafInfinityEvaluation (f.app (Opposite.op ⦋0⦌) c) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.evaluateFunctorAt_pre
    ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map f))
    (ULift.up (SSet.opObjEquiv.symm c))

/-- 前層 ∞ 圏の対象は、元の反変な空間値 ∞ 関手と全単射。 -/
def presheafInfinityObjectEquiv (C : SSet.{u}) :
    ((SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) ≃
      (PresheafInfinity C) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _

/-- 対象として表示した前層の評価は、元の ∞ 関手の実際の頂点での値。 -/
lemma presheafInfinityEvaluation_object {C : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (c : C _⦋0⦌) :
    (presheafInfinityEvaluation c).app (Opposite.op ⦋0⦌)
      (presheafInfinityObjectEquiv C F) =
        F.app (Opposite.op ⦋0⦌) (ULift.up (SSet.opObjEquiv.symm c)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex _ F

/-- 空間を同じ底上の定値前層へ送る ∞ 関手。 -/
def constantPresheafInfinity (C : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} ⟶ PresheafInfinity C :=
  curry (snd ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 定値前層を任意の頂点で評価すると、元の空間と全高次の射を厳密に回収する。 -/
lemma constantPresheafInfinity_evaluation {C : SSet.{u}} (c : C _⦋0⦌) :
    constantPresheafInfinity C ≫ presheafInfinityEvaluation c = 𝟙 _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} := by
  rw [constantPresheafInfinity, presheafInfinityEvaluation, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
