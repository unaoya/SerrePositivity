module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.SiteLiftSectionsCone
public import SerrePositivity.InfinityCategories.Sheaves.NativeSheafRepresentableCoefficients
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.UniverseConeRestriction

/-!
概要：元の切断錐の制限を、持ち上げた site 上の表現可能値の全錐へ移す。
方針：元の図式の移送での制限、join の宇宙同型の自然性、表現可能後合成を順に使う。
  文献対応：HTT 6.2.2.6、Kerodon §7.1（Tag 02H1）の指定極限の計算。
使われ方：任意の準圏係数の切断で局所同値を検出する。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
namespace SerrePositivity.InfinityCategories.Sheaves

/-- 同じ錐を制限することは、site を持ち上げて表現可能関手を後合成することと可換。 -/
@[cite HTT "6.2.2.6" (partial := special) "小さい通常の site における切断錐の制限と表現可能値の照合。"]
lemma siteLift_representable_restrictSectionsCone_val :
  ∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
  ∀ {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (O : Presheaf C E)
   (c : JoinCone (sectionsOfDiagram Q O)) (x : E _⦋0⦌),
  let F := (asSmallSiteShapeIso C).inv ≫ O;
  let G := (SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ covariantRepresentableInfinity x;
  let a := siteLiftPresheafMap φ;
  let t := mapJoinCone (covariantRepresentableInfinity x)
   (JoinCone.ulift.{u + 1, u + 2} (siteLiftSectionsCone Q O c));
   (SetWeight.restrictSectionsCone a G t).val =
   (mapJoinCone (covariantRepresentableInfinity x)
     (JoinCone.ulift.{u + 1, u + 2}
      (siteLiftSectionsCone P O (SetWeight.restrictSectionsCone φ O c)))).val := by
  intro C hC E hE P Q φ O c x F G a t
  let U := SSet.uliftFunctor.{u + 2, u + 1}
  let Y := covariantRepresentableInfinity x
  let b := nerveMap a.mapElements
  let d := siteLiftSectionsCone Q O c
  let e := siteLiftSectionsCone P O (SetWeight.restrictSectionsCone φ O c)
  have h := siteLiftSectionsCone_restrict φ O c
  have h₀ : (restrictJoinCone d b).val = e.val := h
  have h₁ : (JoinCone.ulift.{u + 1, u + 2} (restrictJoinCone d b)).val =
      (JoinCone.ulift.{u + 1, u + 2} e).val := by
    change (uliftConeShapeIso _ 0).inv ≫ U.map (restrictJoinCone d b).val =
      (uliftConeShapeIso _ 0).inv ≫ U.map e.val
    rw [h₀]
  change joinMap (𝟙 _) (U.map b) ≫
      ((JoinCone.ulift.{u + 1, u + 2} d).val ≫ Y) =
    (JoinCone.ulift.{u + 1, u + 2} e).val ≫ Y
  rw [← Category.assoc]
  exact congrArg (fun k => k ≫ Y) ((ulift_restrictJoinCone_val d b).symm.trans h₁)

end SerrePositivity.InfinityCategories.Sheaves
