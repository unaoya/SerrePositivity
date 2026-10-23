module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.SectionsKan

/-!
概要：任意の小さい coherent 空間値図式の全切断を、元の宇宙の Kan 対象へ束ねる。
方針：小さい unstraightening の切断模型と、N の切断の Kan 性・普遍的な評価を使う。
規約：底の quasicategory 性は不要。native な極限錐と極限性はまだ主張しない。
使われ方：F1-4 の一般 coherent 小極限の頂点候補と評価の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 全切断を元の小さい宇宙の Kan 対象に束ねた、極限頂点の候補。 -/
def coherentSpaceSectionsObject : KanObject.{u} :=
  ⟨HomotopyLimits.simplicialSections (smallLeftUnstraighteningProjection F),
    HomotopyLimits.simplicialSections_kanComplex (smallLeftUnstraighteningProjection F)⟩

/-- 元の全切断の Kan 対象が与える、空間の ∞ 圏内の実際の頂点。 -/
def coherentSpaceSectionsVertex : SpaceInfinity.{u} _⦋0⦌ :=
  spaceInfinityVertex (coherentSpaceSectionsObject F)

/-- 頂点から取り出した空間は、元の全切断の台と厳密に一致する。 -/
lemma coherentSpaceSectionsVertex_object :
    (spaceInfinityObject (coherentSpaceSectionsVertex F)).obj =
      HomotopyLimits.simplicialSections (smallLeftUnstraighteningProjection F) :=
  congrArg (fun K : KanObject.{u} ↦ K.obj)
    (spaceInfinityVertexEquiv.left_inv (coherentSpaceSectionsObject F))

/-- 全切断の普遍的な族を、元の小さい unstraightening の全空間で評価する。 -/
def coherentSpaceSectionsEvaluation :
    B ⊗ (coherentSpaceSectionsObject F).obj ⟶ smallLeftUnstraightening F :=
  HomotopyLimits.simplicialSectionsEvaluation (smallLeftUnstraighteningProjection F)

/-- 同じ普遍的な評価は元の底の第一射影を保つ。 -/
lemma coherentSpaceSectionsEvaluation_projection :
    coherentSpaceSectionsEvaluation F ≫ smallLeftUnstraighteningProjection F =
      fst B (coherentSpaceSectionsObject F).obj :=
  HomotopyLimits.simplicialSectionsEvaluation_projection (smallLeftUnstraighteningProjection F)

/-- 任意のパラメータから全切断への射は、同じ底を保つ元の評価の族と全単射。 -/
def coherentSpaceSectionsHomEquiv (A : SSet.{u}) :
    (A ⟶ (coherentSpaceSectionsObject F).obj) ≃
      {s : B ⊗ A ⟶ smallLeftUnstraightening F //
        s ≫ smallLeftUnstraighteningProjection F = fst B A} :=
  HomotopyLimits.simplicialSectionsHomEquiv (smallLeftUnstraighteningProjection F) A

end SerrePositivity.InfinityCategories
