module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningTransformationWitness
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.MappingCylinderOverMono

/-!
概要：恒等の coherent な変換の unstraightening は恒等射と底上の写像空間内で同型。
方針：定値の prism の持ち上げを具体的に作り、可縮な選択との終点の同型を使う。
規約：恒等射との厳密な等式を選択した射に要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、unstraightening の変換への作用の単位則。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：coherent な図式の恒等変換を区間に関して定値な族として表示する。
方針：区間を第二射影で忘れて元の図式に合成する。
規約：区間をテンソルの左因子に置く。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、unstraightening の単位則の入力。 -/
def leftUnstraighteningIdentityTransformation {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  snd (Δ[1] : SSet.{u + 1}) B ≫ F

/-- 概要：恒等変換の両端は元の coherent な図式。
方針：prism の端点を第二射影で忘れる。
規約：i は任意の端点。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、恒等変換の始点・終点条件。 -/
lemma leftUnstraighteningIdentityTransformation_endpoint {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i B ≫ leftUnstraighteningIdentityTransformation F = F := by
  rw [leftUnstraighteningIdentityTransformation, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_snd,
    Category.id_comp]

/-- 概要：恒等変換のための区間に関して定値な pointed space の持ち上げ。
方針：元の unstraightening の pointed space 成分を全区間で固定する。
規約：始点の全空間をパラメーターにする。
使われ方：Kerodon Lemma 5.2.2.13（Tag 02RB）、恒等変換の具体的な持ち上げ。 -/
noncomputable def leftUnstraighteningIdentityLift {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    (Δ[1] : SSet.{u + 1}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u} :=
  snd (Δ[1] : SSet.{u + 1}) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) ≫ pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection F

/-- 概要：定値の pointed space の持ち上げは両端で元の pointed space 成分に等しい。
方針：prism の端点と第二射影を合成する。
規約：i は任意の端点。
使われ方：Kerodon Lemma 5.2.2.13（Tag 02RB）、恒等射の終点との一致。 -/
lemma leftUnstraighteningIdentityLift_endpoint {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _ ≫ leftUnstraighteningIdentityLift F =
      pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection F := by
  rw [leftUnstraighteningIdentityLift, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_snd, Category.id_comp]

/-- 概要：定値の pointed space の持ち上げは元の射影に沿う恒等変換を被覆する。
方針：引き戻しの可換性と第二射影の自然性を使う。
規約：底の変換を厳密に固定した等式。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、恒等射の持ち上げを選択空間へ入れる。 -/
lemma leftUnstraighteningIdentityLift_projection {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    leftUnstraighteningIdentityLift F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) ≫ leftUnstraighteningIdentityTransformation F := by
  change (snd (Δ[1] : SSet.{u + 1}) (pullback _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection F) ≫
    pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (Δ[1] ◁ pullback.snd _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection F) ≫ (snd (Δ[1] : SSet.{u + 1}) B ≫ F)
  rw [Category.assoc, pullback.condition,
    ← Category.assoc (Δ[1] ◁ pullback.snd _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection F), whiskerLeft_snd]
  rfl

/-- 概要：恒等変換に選択した unstraightening の射は、恒等射と底上の写像空間で同型。
方針：定値の具体的な持ち上げの終点と、可縮な選択の終点を比較する。
規約：底 B は任意の単体集合。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、unstraightening の変換への作用の単位則。 -/
noncomputable def leftUnstraighteningTransformationMap_identityIso
    {B : SSet.{u + 1}} (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationMap F F (leftUnstraighteningIdentityTransformation F)
          (leftUnstraighteningIdentityTransformation_endpoint F 0)
          (leftUnstraighteningIdentityTransformation_endpoint F 1)).val
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationMap F F (leftUnstraighteningIdentityTransformation F)
          (leftUnstraighteningIdentityTransformation_endpoint F 0)
          (leftUnstraighteningIdentityTransformation_endpoint F 1)).property)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F)
        (𝟙 _) (Category.id_comp _)) := by
  let W := leftUnstraighteningIdentityLift F
  let h₀ := leftUnstraighteningIdentityTransformation_endpoint F 0
  let h₁ := leftUnstraighteningIdentityTransformation_endpoint F 1
  let hW₀ := leftUnstraighteningIdentityLift_endpoint F 0
  let hWp := leftUnstraighteningIdentityLift_projection F
  let x := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationWitness F
    (leftUnstraighteningIdentityTransformation F) h₀ W hW₀ hWp
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationWitness_endpoint F F
    (leftUnstraighteningIdentityTransformation F) h₀ h₁ W hW₀ hWp (𝟙 _)
    (Category.id_comp _) (by
      rw [Category.id_comp]
      exact leftUnstraighteningIdentityLift_endpoint F 1)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationMapChoiceIso F F
    (leftUnstraighteningIdentityTransformation F) h₀ h₁ x ≪≫
      eqToIso (congrArg SSet.HomotopyCategory.mk he)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
