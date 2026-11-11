module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedPrismSourceFiber
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.PrismBoundaryRecovery

/-!
概要：始点も動く pointed-space lift の普遍 prism と端点評価の公式。
方針：始点の普遍評価と fiber 値の終点評価を全空間で比較する。
規約：全ての始点写像を許す空間を用いる。
使われ方：同時端点制限の Kan fibration 性の証明。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 概要：二つの Kan 複体の直積は Kan 複体。
方針：二射影で独立にホーンを充填して組にする。
規約：直積は Cartesian monoidal tensor を使う。
使われ方：始点と区間を同時に動かすパラメーター空間。 -/
lemma prismParameterProduct_kanComplex (X Y : SSet.{u}) [KanComplex X] [KanComplex Y] :
    KanComplex (X ⊗ Y) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_of_rightHornFillers
  intro n i _ a
  obtain ⟨F, hF⟩ := KanComplex.hornFilling (a ≫ fst X Y)
  obtain ⟨G, hG⟩ := KanComplex.hornFilling (a ≫ snd X Y)
  refine ⟨lift F G, ?_⟩
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [Category.assoc, lift_fst] using hF.symm
  · simpa only [Category.assoc, lift_snd] using hG.symm

/-- 概要：Kan パラメーター上の全 lift 空間は Kan 複体。
方針：パラメーター側でホーンを充填し、trivial Kan 射影で持ち上げる。
規約：初期値データは任意で底の Kan 性は要求しない。
使われ方：始点も動く全 pointed-space lift 空間の Kan 性。 -/
instance prismLiftSpace_kanComplex {E B K L : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    [KanComplex L] (d : L ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).pt) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpace p K d) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_of_rightHornFillers
  intro n i _ a
  obtain ⟨F, hF⟩ := KanComplex.hornFilling (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceProjection p K d)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceProjection p K d)
    (horn (n + 1) i).ι inferInstance
  let sq : CommSq a (horn (n + 1) i).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceProjection p K d) F := ⟨hF⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 概要：全 pointed-space lift 空間は Kan 複体。
方針：始点 fiber の関手空間と区間写像空間の Kan 性を使う。
規約：係数 K は任意。
使われ方：left fibration から全ホーン充填への移行。 -/
instance pointedPrismLiftSpace_kanComplex (K : SSet.{u + 1})
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftSpace K s t) := by
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismParameterSpace K s t) := by
    exact prismParameterProduct_kanComplex
      ((ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace s t)
  change KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismData K s t))
  infer_instance

/-- 概要：普遍 prism の始点は始点射の fiber 値の評価。
方針：動く初期値の始点公式と内部 Hom の評価の自然性を使う。
規約：始点写像も全ての高次パラメーターとともに動く。
使われ方：相対ホーンの始点条件の確認。 -/
lemma pointedPrismEvaluation_zero (K : SSet.{u + 1}) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpacePrism _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismData K s t) =
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftSource K s t) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s := by
  calc
    _ = (K ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftParameters K s t) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismInitial K s t :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpacePrism_start _ _ _ _
    _ = _ := by
      change (K ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftParameters K s t) ≫
    (K ◁ fst _ _) ≫ uncurry (𝟙 ((ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s))) ≫ _ = _
      rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
      change (K ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftSource K s t) ≫ uncurry (𝟙 _) ≫ _ = _
      rw [← Category.assoc, ← uncurry_natural_left, Category.comp_id]

/-- 概要：普遍 prism の終点は終点射の fiber 値の評価。
方針：終点を fiber へ持ち上げた定義を展開する。
規約：厳密な等式。
使われ方：相対ホーンの終点条件の確認。 -/
lemma pointedPrismEvaluation_one (K : SSet.{u + 1}) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpacePrism _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismData K s t) =
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftEndpoint K s t) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection t := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftEndpoint, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceEndpoint]
  rw [uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
  rfl

/-- 概要：任意のパラメーター族で普遍初期値を評価する式。
方針：内部 Hom の評価の自然性を使う。
規約：始点と区間の両パラメーターを持つ射 g は任意。
使われ方：充填した prism の始点を lift 空間の初期値に戻す。 -/
lemma pointedPrismInitial_precomp {K L : SSet.{u + 1}}
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) (g : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismParameterSpace K s t) :
    (K ◁ g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismInitial K s t =
      uncurry (g ≫ fst _ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s := by
  change (K ◁ g) ≫ (K ◁ fst _ _) ≫ uncurry (𝟙 _) ≫ _ = _
  rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    ← Category.assoc, ← uncurry_natural_left, Category.comp_id]

/-- 概要：任意のパラメーター族で普遍的な底を評価する式。
方針：区間写像空間の展開の自然性を使う。
規約：係数 K は底の区間の評価では忘れる。
使われ方：充填した prism の底を lift 空間の底に戻す。 -/
lemma pointedPrismBase_precomp {K L : SSet.{u + 1}}
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) (g : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismParameterSpace K s t) :
    (Δ[1] ◁ (K ◁ g)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismBase K s t =
      (Δ[1] ◁ snd K L) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (g ≫ snd _ _) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp
    (snd ((ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace s t))
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace s t))
  simp only [Category.comp_id] at h
  rw [h]
  rfl

/-- 概要：普遍 prism の底はその区間パラメーターの評価。
方針：動く初期値の底の式とパラメーターの底の評価式を合成する。
規約：区間族全体についての等式。
使われ方：既定のホーン上の底の条件を確認する。 -/
lemma pointedPrismEvaluation_base (K : SSet.{u + 1}) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpacePrism _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismData K s t) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (Δ[1] ◁ snd K _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftParameters K s t ≫ snd _ _) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpacePrism_base _ _ _ _).trans (pointedPrismBase_precomp s t _)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
