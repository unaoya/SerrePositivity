module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceRoofAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsFiberFunctorLaws

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じ fiber のパラメータ入力と元の全 augmentation の厳密な制限。
方針：既存の同じ図式・射・指定同型の合成則を使う。
規約：元の全パラメータと指定された値を保持する。
使われ方：IS-W2 R03h・R03d の native Hom と同じ roof の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open scoped _root_.Simplicial
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot

variable (A : Type u) [CommRing A]
local instance jointRoofParameterLawModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointRoofParameterLawFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 同じfiberの反対圏から、元の全augmentationの同じパラメータへの入力。 -/
def strictBETotJointRoofParameterIndex (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    ((simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⥤
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameIndex A :=
  (simplicialElementsFiberFunctor (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A) P ⋙
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceParameterIndex A).leftOp

/-- 同じパラメータ入力の対象は、元の試験対象と同じ単体次数。 -/
theorem strictBETotJointRoofParameterIndex_obj (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofParameterIndex A P).obj s =
      (AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra × SimplexCategory ⥤ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameIndex A).obj
        ((AsSmall.down.obj P).1.unop, s.unop.obj.unop) := rfl

/-- 同じパラメータ入力の射は、恒等な試験対象成分と元の単体作用素。 -/
theorem strictBETotJointRoofParameterIndex_map (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A)
    {s t : ((simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ}
    (f : s ⟶ t) :
    HEq ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofParameterIndex A P).map f)
      ((AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra × SimplexCategory ⥤ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameIndex A).map
        ((𝟙 (AsSmall.down.obj P).1.unop, f.unop.down.hom.unop) :
          ((AsSmall.down.obj P).1.unop, s.unop.obj.unop) ⟶
            ((AsSmall.down.obj P).1.unop, t.unop.obj.unop))) := by
  apply heq_of_eq
  apply ULift.ext
  apply Prod.ext
  · rfl
  · change ((simplicialElementsFiberFunctor (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A) P).map
      f.unop).hom.2.unop = f.unop.down.hom.unop
    exact congrArg Quiver.Hom.unop
      (sameSimplicialElementsFiberFunctor_degree (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A) P f.unop)

private theorem sameFunctor_map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {x y x' y' : C} (hx : x = x') (hy : y = y')
    (f : x ⟶ y) (g : x' ⟶ y') (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst x'
  subst y'
  cases eq_of_heq h
  rfl

/-- 元の全augmentationの評価端は、同じfiberのroof図式と一致する。 -/
theorem strictBETotJointRoofParameterIndex_evaluation (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofParameterIndex A P ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameEvaluation A =
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameDiagram A P := by
  refine CategoryTheory.Functor.hext (fun s => ?_) ?_
  · change (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameEvaluation A).obj
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofParameterIndex A P).obj s) = _
    rw [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofParameterIndex_obj]
    rfl
  · intro s t f
    have hh := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.sameFunctor_map_heq (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameEvaluation A)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofParameterIndex_obj A P s) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofParameterIndex_obj A P t)
      _ _ (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofParameterIndex_map A P f)
    have hn : HEq
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameEvaluation A).map
          ((AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra × SimplexCategory ⥤ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameIndex A).map
            ((𝟙 (AsSmall.down.obj P).1.unop, f.unop.down.hom.unop) :
          ((AsSmall.down.obj P).1.unop, s.unop.obj.unop) ⟶
            ((AsSmall.down.obj P).1.unop, t.unop.obj.unop))))
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameDiagram A P).map f) := by
      change HEq
        ((AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).map
          (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A).map (𝟙 (AsSmall.down.obj P).1.unop)).app s.unop.obj.unop ≫
            ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A).obj (AsSmall.down.obj P).1.unop).map
              f.unop.down.hom.unop)) _
      rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
      rfl
    exact hh.trans hn

/-- 元の全augmentationの定値端は、元の同じ試験対象の定値図式と一致する。 -/
theorem strictBETotJointRoofParameterIndex_constant (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofParameterIndex A P ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameConstant A =
      (CategoryTheory.Functor.const _).obj
        (modelRelativeObject (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra (AsSmall.down.obj P).1.unop) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro s t f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).map
    (𝟙 (AsSmall.down.obj P).1.unop ≫ 𝟙 _) = 𝟙 _
  rw [Category.id_comp, CategoryTheory.Functor.map_id]

private theorem sameNatTrans_heq {I C : Type*} [Category I] [Category C]
    {F G F' G' : I ⥤ C} (hF : F = F') (hG : G = G')
    (η : F ⟶ G) (η' : F' ⟶ G')
    (ha : ∀ i, HEq (η.app i) (η'.app i)) : HEq η η' := by
  subst F'
  subst G'
  apply heq_of_eq
  ext i
  exact eq_of_heq (ha i)

/-- 元の同じ全augmentationの引き戻しは、同じfull augmentationそのもの。 -/
theorem strictBETotJointRoofParameterIndex_augmentation
    (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    HEq (CategoryTheory.Functor.whiskerLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofParameterIndex A P)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation A))
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFullAugmentation A P) := by
  apply _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.sameNatTrans_heq (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofParameterIndex_evaluation A P)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofParameterIndex_constant A P)
  intro s
  exact heq_of_eq (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFullAugmentation_original A P s).symm

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
