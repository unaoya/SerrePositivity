module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotProbeSourceFunctor
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotFrameHomInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOpposite
public import Mathlib.CategoryTheory.Functor.Currying

/-!
概要：元の両変数raw Homと正本Hom∞の全比較の二つの入力を、同じ底・宇宙に揃える。
方針：元のuncurry・AsSmall・ULift・Ex∞と、同じCAlg源の二つの射影を合成する。
規約：IS-W2 R02〜R03の既存図式の全係数表示。二入力間の全同型はここでは主張しない。
使われ方：固定始域ごとの比較と両変数のcoherentな比較を型で区別する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet MonoidalCategory
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open scoped Simplicial
variable (A : Type u) [CommRing A]
local instance strictBETotJointHomInputModel : ModelCategory (operad A).Algebra := modelCategory A

local instance strictBETotJointHomInputFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance strictBETotJointHomInputCof (X : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A X) := framedLimitProbe_cofibrant A X

/-- 元の両変数の圏を同じ大きい通常の添字にする。 -/
abbrev strictBETotJointHomIndex :=
  AsSmall.{u+1} ((operad A).Algebraᵒᵖ × (operad A).Algebra)

/-- 元のprobeつきraw Homを、同じ二変数の積でuncurryする。 -/
def strictBETotJointRawHom :
    ((operad A).Algebraᵒᵖ × (operad A).Algebra) ⥤ SSet.{u} :=
  Functor.uncurry.obj (strictBETotProbeRightHomBifunctor A)

/-- 元の両変数raw Homを、同じ係数の宇宙変更とEx∞に送る全Kan図式。 -/
def strictBETotJointRawHomKan : strictBETotJointHomIndex A ⥤ KanObject.{u+1} :=
  AsSmall.down ⋙ FrameHom.kanHomFamily (strictBETotJointRawHom A ⋙ SSet.uliftFunctor.{u+1,u})

/-- 両変数raw Homの同じcoherentな実現。 -/
def strictBETotJointRawHomCoherent :
    (SSet.uliftFunctor.{u+2,u+1}).obj (nerve (strictBETotJointHomIndex A)) ⟶ SpaceInfinity.{u+1} :=
  kanDiagramCoherentNerve (strictBETotJointRawHomKan A)

/-- 同じ積添字の第一射影を、同じモデル源の反対添字にする。 -/
def strictBETotJointHomSourceIndex :
    strictBETotJointHomIndex A ⥤ (AsSmall.{u+1} (operad A).Algebra)ᵒᵖ :=
  AsSmall.down ⋙ CategoryTheory.Prod.fst (operad A).Algebraᵒᵖ (operad A).Algebra ⋙
    (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).op

/-- 同じ積添字の第二射影を、同じモデル源の添字にする。 -/
def strictBETotJointHomTargetIndex :
    strictBETotJointHomIndex A ⥤ AsSmall.{u+1} (operad A).Algebra :=
  AsSmall.down ⋙ CategoryTheory.Prod.snd (operad A).Algebraᵒᵖ (operad A).Algebra ⋙ AsSmall.up

/-- 同じ元のCAlg源の両変数を組にした、正本Hom∞の底への指定射。 -/
def strictBETotJointNativeHomInput :
    nerve (strictBETotJointHomIndex A) ⟶ (CAlg_R A).op ⊗ CAlg_R A :=
  CartesianMonoidalCategory.lift
    (nerveMap (strictBETotJointHomSourceIndex A) ≫
      (nerveOppositeIso (C := AsSmall.{u+1} (operad A).Algebra)).inv ≫
        SSet.opFunctor.map (strictBETotModelSource A))
    (nerveMap (strictBETotJointHomTargetIndex A) ≫ strictBETotModelSource A)

/-- 同じCAlg源の正本の二変数Hom∞を、上の同じ元の底へ引き戻す。 -/
def strictBETotJointNativeHomCoherent :
    (SSet.uliftFunctor.{u+2,u+1}).obj (nerve (strictBETotJointHomIndex A)) ⟶ SpaceInfinity.{u+1} :=
  (SSet.uliftFunctor.{u+2,u+1}).map (strictBETotJointNativeHomInput A) ≫
    twistedArrowHomInfinity (CAlg_R A)

/-- 元の始域を固定する、同じ大きい通常の添字の包含。 -/
def strictBETotJointHomFixSource (X : (operad A).Algebra) :
    AsSmall.{u+1} (operad A).Algebra ⥤ strictBETotJointHomIndex A :=
  AsSmall.down ⋙ CategoryTheory.Prod.sectR (Opposite.op X) (operad A).Algebra ⋙ AsSmall.up

/-- uncurryの始域を固定すると、元の同じ実right frame Homに戻る。 -/
theorem strictBETotJointRawHom_fixSource (X : (operad A).Algebra) :
    CategoryTheory.Prod.sectR (Opposite.op X) (operad A).Algebra ⋙ strictBETotJointRawHom A =
      rightFrameHom (rightFrameFamily A) (framedLimitProbe A X) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro Y Z f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (((strictBETotProbeRightHomBifunctor A).map (𝟙 (Opposite.op X))).app Y) ≫
    ((strictBETotProbeRightHomBifunctor A).obj (Opposite.op X)).map f =
      ((strictBETotProbeRightHomBifunctor A).obj (Opposite.op X)).map f
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- 同じ全Kan入力の始域制限は、既存の全frame比較の第零図式そのもの。 -/
theorem strictBETotJointRawHomKan_fixSource (X : (operad A).Algebra) :
    strictBETotJointHomFixSource A X ⋙ strictBETotJointRawHomKan A =
      FrameHom.rightFrameHammockKanDiagram
        ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
          (framedLimitProbe A X)) (rightFrameFamily A) 0 := by
  change AsSmall.down ⋙ FrameHom.kanHomFamily
      ((CategoryTheory.Prod.sectR (Opposite.op X) (operad A).Algebra ⋙
        strictBETotJointRawHom A) ⋙ SSet.uliftFunctor.{u+1,u}) =
    AsSmall.down ⋙ FrameHom.kanHomFamily
      (rightFrameHom (rightFrameFamily A) (framedLimitProbe A X) ⋙ SSet.uliftFunctor.{u+1,u})
  rw [strictBETotJointRawHom_fixSource]

/-- 同じcoherent入力の始域制限も、既存の第零全比較のcoherentな入力に厳密に等しい。 -/
theorem strictBETotJointRawHomCoherent_fixSource (X : (operad A).Algebra) :
    (SSet.uliftFunctor.{u+2,u+1}).map (nerveMap (strictBETotJointHomFixSource A X)) ≫
      strictBETotJointRawHomCoherent A =
    FrameHom.rightFrameHammockCoherentDiagram
      ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
        (framedLimitProbe A X)) (rightFrameFamily A) 0 := by
  change _ ≫ kanDiagramCoherentNerve (strictBETotJointRawHomKan A) = _
  rw [kanDiagramCoherentNerve_precomp, strictBETotJointRawHomKan_fixSource]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
