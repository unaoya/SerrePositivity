module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsFiberFunctorLaws

/-!
概要：同じ fiber のパラメータ入力と元の全 augmentation の厳密な制限。
方針：既存の同じ図式・射・指定同型の合成則を使う。
規約：元の全パラメータと指定された値を保持する。
使われ方：IS-W2 R03h・R03d の native Hom と同じ roof の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.EInfinity.FrameHom
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open scoped Simplicial
namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]
local instance jointRoofParameterLawModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointRoofParameterLawFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 同じfiberの反対圏から、元の全augmentationの同じパラメータへの入力。 -/
def strictBETotJointRoofParameterIndex (P : strictBETotJointHomIndex A) :
    ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⥤
      strictBETotJointSourceFrameIndex A :=
  (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P ⋙
    strictBETotJointSourceParameterIndex A).leftOp

/-- 同じパラメータ入力の対象は、元の試験対象と同じ単体次数。 -/
theorem strictBETotJointRoofParameterIndex_obj (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    (strictBETotJointRoofParameterIndex A P).obj s =
      (AsSmall.up : (operad A).Algebra × SimplexCategory ⥤ strictBETotJointSourceFrameIndex A).obj
        ((AsSmall.down.obj P).1.unop, s.unop.obj.unop) := rfl

/-- 同じパラメータ入力の射は、恒等な試験対象成分と元の単体作用素。 -/
theorem strictBETotJointRoofParameterIndex_map (P : strictBETotJointHomIndex A)
    {s t : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ}
    (f : s ⟶ t) :
    HEq ((strictBETotJointRoofParameterIndex A P).map f)
      ((AsSmall.up : (operad A).Algebra × SimplexCategory ⥤ strictBETotJointSourceFrameIndex A).map
        ((𝟙 (AsSmall.down.obj P).1.unop, f.unop.down.hom.unop) :
          ((AsSmall.down.obj P).1.unop, s.unop.obj.unop) ⟶
            ((AsSmall.down.obj P).1.unop, t.unop.obj.unop))) := by
  apply heq_of_eq
  apply ULift.ext
  apply Prod.ext
  · rfl
  · change ((simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P).map
      f.unop).hom.2.unop = f.unop.down.hom.unop
    exact congrArg Quiver.Hom.unop
      (sameSimplicialElementsFiberFunctor_degree (strictBETotJointSourceCoefficients A) P f.unop)

private theorem sameFunctor_map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {x y x' y' : C} (hx : x = x') (hy : y = y')
    (f : x ⟶ y) (g : x' ⟶ y') (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst x'
  subst y'
  cases eq_of_heq h
  rfl

/-- 元の全augmentationの評価端は、同じfiberのroof図式と一致する。 -/
theorem strictBETotJointRoofParameterIndex_evaluation (P : strictBETotJointHomIndex A) :
    strictBETotJointRoofParameterIndex A P ⋙ strictBETotJointSourceFrameEvaluation A =
      strictBETotJointSourceRoofFrameDiagram A P := by
  refine CategoryTheory.Functor.hext (fun s => ?_) ?_
  · change (strictBETotJointSourceFrameEvaluation A).obj
      ((strictBETotJointRoofParameterIndex A P).obj s) = _
    rw [strictBETotJointRoofParameterIndex_obj]
    rfl
  · intro s t f
    have hh := sameFunctor_map_heq (strictBETotJointSourceFrameEvaluation A)
      (strictBETotJointRoofParameterIndex_obj A P s) (strictBETotJointRoofParameterIndex_obj A P t)
      _ _ (strictBETotJointRoofParameterIndex_map A P f)
    have hn : HEq
        ((strictBETotJointSourceFrameEvaluation A).map
          ((AsSmall.up : (operad A).Algebra × SimplexCategory ⥤ strictBETotJointSourceFrameIndex A).map
            ((𝟙 (AsSmall.down.obj P).1.unop, f.unop.down.hom.unop) :
          ((AsSmall.down.obj P).1.unop, s.unop.obj.unop) ⟶
            ((AsSmall.down.obj P).1.unop, t.unop.obj.unop))))
        ((strictBETotJointSourceRoofFrameDiagram A P).map f) := by
      change HEq
        ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
          (((strictBETotJointSourceFrame A).map (𝟙 (AsSmall.down.obj P).1.unop)).app s.unop.obj.unop ≫
            ((strictBETotJointSourceFrame A).obj (AsSmall.down.obj P).1.unop).map
              f.unop.down.hom.unop)) _
      rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
      rfl
    exact hh.trans hn

/-- 元の全augmentationの定値端は、元の同じ試験対象の定値図式と一致する。 -/
theorem strictBETotJointRoofParameterIndex_constant (P : strictBETotJointHomIndex A) :
    strictBETotJointRoofParameterIndex A P ⋙ strictBETotJointSourceFrameConstant A =
      (CategoryTheory.Functor.const _).obj
        (modelRelativeObject (operad A).Algebra (AsSmall.down.obj P).1.unop) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro s t f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
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
    (P : strictBETotJointHomIndex A) :
    HEq (CategoryTheory.Functor.whiskerLeft (strictBETotJointRoofParameterIndex A P)
      (strictBETotJointSourceFrameAugmentation A))
      (strictBETotJointSourceRoofFullAugmentation A P) := by
  apply sameNatTrans_heq (strictBETotJointRoofParameterIndex_evaluation A P)
    (strictBETotJointRoofParameterIndex_constant A P)
  intro s
  exact heq_of_eq (strictBETotJointSourceRoofFullAugmentation_original A P s).symm

end SerrePositivity.EInfinity.BarrattEccles
