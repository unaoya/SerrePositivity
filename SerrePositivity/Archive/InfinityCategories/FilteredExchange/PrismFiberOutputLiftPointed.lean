module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PrismFiberOutputLift
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallRelativeFiberHomPointed
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RelativeConstFiberEvaluation

/-!
概要：旧 prism 出力の単体的表示を、元の全相対族の pointed 成分へ厳密に同定する。
方針：fiber Hom の持ち上げの座標式に縮小を前合成し、縮小同型と底の輸送を消す。
規約：全単体パラメータを保持。使われ方：新しい終点評価との指定類の一致。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
local notation "pF" => smallLeftUnstraighteningProjection F
local notation "pJ" => smallLeftUnstraighteningProjection J
local notation "i" => vertexFiberι pF b
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "m" => smallUnstraighteningSourceRestriction F i
local notation "c" => Over.Hom.left m ≫ leftUnstraighteningProjection F
local notation "R" => relativeFunctorSpace (leftUnstraighteningProjection J) c

/-- 旧出力を全パラメータで展開し元の pointed 始点族へ含めると、元の全相対族に一致。 -/
lemma coherentPrismFiberOutputLift_pointed :
    uncurry (coherentPrismFiberOutputLift F J b) ≫ coherentCospanFiberPointedSource J b =
      relativeFunctorUncurry (𝟙 R) ≫ pullback.fst pointedSpaceProjection J := by
  have hc : coherentPrismEndpointShrink F J b ≫
      (smallUnstraighteningSourceRelativeIso J (i ≫ pF)).hom =
      eqToHom (congrArg (relativeFunctorSpace (leftUnstraighteningProjection J)) (m).w) := by
    simp only [coherentPrismEndpointShrink, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [coherentPrismFiberOutputLift, uncurry_natural_left, Category.assoc,
    smallRelativeFiberHom_pointed J (i ≫ pF) b (vertexFiberι_comp pF b), ← Category.assoc,
    ← relativeFunctorUncurry_naturality, hc]
  have ht := relativeFunctorUncurry_transport (leftUnstraighteningProjection J) (m).w (𝟙 R)
  simpa only [eqToIso.hom, Category.id_comp] using
    congrArg (fun k => k ≫ pullback.fst pointedSpaceProjection J) ht

end SerrePositivity.InfinityCategories.F2
