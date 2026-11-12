module
public import SerrePositivity.KST.Fibration.Relative.ClosedFlagFunctor
public import SerrePositivity.KST.Fibration.WeakStringConstantNaturality

/-!
概要：元の B から P 相対旗への定数旗とその実現射。
方針：既存の同値辺の定数旗を、零 cofiber の P 所属で元の全部分旗へ含める。
規約：B・P のみ。使われ方：共通 fiber 定理の元の c_B。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：全同値旗は P 相対旗に属する。方針：各辺の cofiber が零。
規約：P は零を含む。使われ方：元の定数旗を含める。 -/
lemma coreFlag_mem {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (n : SimplexCategory) (v : ((ihom (stdSimplex.obj n)).obj B.carrier) _⦋0⦌)
    (hv : weakStringPredicate (𝟙 (flagAmbient B)) n v) :
    (closedFlagStablePredicate P n).predicate v := by
  intro α
  have ha := (weakStringPredicate_iff_restrictions (𝟙 (flagAmbient B)) n v).1 hv α
  have hz := (weakArrowClosedPredicate_iff (𝟙 (flagAmbient B)) _).2 ha
  exact P.zero_mem hz

/-- 概要：全同値旗を P 相対旗へ含める完全関手。
方針：元の周囲図式上の恒等射を全部分圏へ制限。
規約：全自然変換を保持。使われ方：同じ定数旗の実現。 -/
def coreFlagInclusion {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (n : SimplexCategory) : weakStringModel (𝟙 (flagAmbient B)) n ⟶ closedFlagModel P n :=
  closedStableMap (weakStringClosedPredicate (𝟙 (flagAmbient B)) n)
    (closedFlagStablePredicate P n) (𝟙 _) (fun v hv => coreFlag_mem P n v hv)

/-- 概要：元の全同値旗の包含後の値。方針：完全制限の包含公式。
規約：周囲で恒等。使われ方：全単体的照合。 -/
lemma coreFlagInclusion_ι {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (n : SimplexCategory) : (coreFlagInclusion P n).val ≫
      (closedStableInclusion (closedFlagStablePredicate P n)).val =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate (𝟙 (flagAmbient B)) n)).ι := by
  exact (congrArg Subtype.val (closedStableMap_inclusion _ _ _ _)).trans (Category.comp_id _)

/-- 概要：元の B からの同じ定数旗。方針：既存定数旗と全同値旗包含の合成。
規約：入力対象を変更しない。使われ方：c_B の各次数。 -/
def closedFlagConstant {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (n : SimplexCategory) : B ⟶ closedFlagModel P n :=
  weakStringConstantExact (𝟙 (flagAmbient B)) n ≫ coreFlagInclusion P n

/-- 概要：定数旗は元の周囲の定数図式そのもの。
方針：同じ包含と既存定数旗の回収公式。規約：厳密等号。使われ方：元の射の保持。 -/
lemma closedFlagConstant_ι {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (n : SimplexCategory) : (closedFlagConstant P n).val ≫
      (closedStableInclusion (closedFlagStablePredicate P n)).val =
        curry (snd (stdSimplex.obj n) B.carrier) := by
  change ((weakStringConstantExact (𝟙 (flagAmbient B)) n).val ≫
    (coreFlagInclusion P n).val) ≫ _ = _
  rw [Category.assoc, coreFlagInclusion_ι, weakStringConstantExact_ι]
  rfl

/-- 概要：同じ定数旗の全次数自然性。方針：元の全関手圏の前合成で検証。
規約：全面・全退化。使われ方：実現前の c_B。 -/
lemma closedFlagConstant_reindex {B : StableModel.{u}} (P : ClosedStablePredicate B)
    {m n : SimplexCategory} (θ : m ⟶ n) :
    closedFlagConstant P n ≫ closedFlagMap P θ = closedFlagConstant P m := by
  apply closedStableInclusion_cancel (closedFlagStablePredicate P m)
  rw [Category.assoc, closedFlagMap_inclusion, ← Category.assoc]
  apply Subtype.ext
  change ((closedFlagConstant P n).val ≫ (closedStableInclusion _).val) ≫
    (pre (stdSimplex.map θ)).app B.carrier =
      (closedFlagConstant P m).val ≫ (closedStableInclusion _).val
  rw [closedFlagConstant_ι, closedFlagConstant_ι]
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
  exact whiskerRight_snd (stdSimplex.map θ) B.carrier

/-- 概要：F(B) から全旗の F 値への定数旗の自然変換。
方針：元の完全定数旗へ F を適用。規約：F は core S 実現。
使われ方：元の対角実現への射。 -/
def closedFlagRealizationConstant {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj (coreSRealizationFunctor.obj B) ⟶
      closedFlagRealizationDiagram P where
  app n := coreSRealizationFunctor.map (closedFlagConstant P n.unop)
  naturality {n m} θ := by
    change 𝟙 _ ≫ coreSRealizationFunctor.map (closedFlagConstant P m.unop) =
      coreSRealizationFunctor.map (closedFlagConstant P n.unop) ≫
        coreSRealizationFunctor.map (closedFlagMap P θ.unop)
    rw [Category.id_comp]
    exact (congrArg coreSRealizationFunctor.map
      (closedFlagConstant_reindex P θ.unop)).symm.trans
        (coreSRealizationFunctor.map_comp _ _)

/-- 概要：仕様の元の定数旗射 c_B。方針：定数対象の対角同型と全旗の実射を合成。
規約：局所化前の SSet 射。使われ方：指定零旗上の実 homotopy fiber。 -/
def closedRelativeConstant {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    coreSRealizationFunctor.obj B ⟶ closedRelativeRealization P :=
  (constantSSetDiagonalIso (coreSRealizationFunctor.obj B)).inv ≫
    simplicialDiagonalFunctor.map (closedFlagRealizationConstant P)

end SerrePositivity.KST.Fibration.Relative
