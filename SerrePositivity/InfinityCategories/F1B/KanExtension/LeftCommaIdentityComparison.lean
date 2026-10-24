module

public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaContraction
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaLiftHomotopy

/-!
概要：oriented comma の元の添字の恒等矢印から各矢印への比較を構成する。
方針：標的を固定する comma の変形を反転し、二重反転の底の同型を戻す。
規約：元の添字への射影は時間に定値、底への射影は標準指定変換。
使われ方：候補図式の指定変換と局所余錐の輸送をつなぐ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：元の添字の恒等矢印から oriented comma の各矢印への指定ホモトピー。
方針：反転前の comma の標的を固定した変形を反転する。
規約：終点は oriented comma の恒等射。
使われ方：局所添字を comma fiber へ写した図式と元の添字上の図式を比較する。 -/
def kanLeftCommaIdentityComparison {K C : SSet.{u}} (δ : K ⟶ C) :
    SSet.Homotopy (kanLeftCommaSource δ ≫ kanLeftCommaInclusion δ) (𝟙 (kanLeftComma δ)) := by
  have he : kanLeftCommaSource δ ≫ kanLeftCommaInclusion δ = SSet.opFunctor.map
      (unitCommaTarget (SSet.opFunctor.map δ) ≫
        unitCommaIdentityFamily (SSet.opFunctor.map δ)) := by
    change SSet.opFunctor.map (unitCommaTarget (SSet.opFunctor.map δ)) ≫
      (SSet.opFunctorCompOpFunctorIso.app K).hom ≫
        (SSet.opFunctorCompOpFunctorIso.app K).inv ≫
          SSet.opFunctor.map (unitCommaIdentityFamily (SSet.opFunctor.map δ)) = _
    rw [Iso.hom_inv_id_assoc]
    rfl
  let T := SerrePositivity.InfinityCategories.homotopyOpposite (SerrePositivity.InfinityCategories.F1B.unitCommaContraction (SSet.opFunctor.map δ))
  refine { h := T.h, h₀ := ?_, h₁ := ?_, rel := T.rel }
  · rw [T.h₀, he]
    rfl
  · rw [T.h₁, CategoryTheory.Functor.map_id]
    rfl

/-- 概要：oriented comma の比較は元の添字を固定する。
方針：反転前の標的固定条件を反転して二重反転を戻す。
規約：時間に定値な射との厳密な等式。
使われ方：元の図式 F₀ を局所余錐の輸送中に固定する。 -/
lemma kanLeftCommaIdentityComparison_source {K C : SSet.{u}} (δ : K ⟶ C) :
    (kanLeftCommaIdentityComparison δ).h ≫ kanLeftCommaSource δ =
      fst (kanLeftComma δ) Δ[1] ≫ kanLeftCommaSource δ := by
  have hv : (SerrePositivity.InfinityCategories.homotopyOpposite (SerrePositivity.InfinityCategories.F1B.unitCommaContraction (SSet.opFunctor.map δ))).h ≫
      SSet.opFunctor.map (unitCommaTarget (SSet.opFunctor.map δ)) =
        fst (kanLeftComma δ) Δ[1] ≫
          SSet.opFunctor.map (unitCommaTarget (SSet.opFunctor.map δ)) := by
    rw [← kanHomotopyOpposite_postcomp_h]
    dsimp only [SerrePositivity.InfinityCategories.homotopyOpposite, functorHomotopyPostcomp]
    rw [SerrePositivity.InfinityCategories.F1B.unitCommaContraction_target]
    rfl
  change (SerrePositivity.InfinityCategories.homotopyOpposite (SerrePositivity.InfinityCategories.F1B.unitCommaContraction (SSet.opFunctor.map δ))).h ≫
    SSet.opFunctor.map (unitCommaTarget (SSet.opFunctor.map δ)) ≫
      (SSet.opFunctorCompOpFunctorIso.app K).hom = _
  rw [← Category.assoc, hv, Category.assoc]
  rfl

/-- 概要：oriented comma の比較の底への射影は標準指定変換。
方針：反転前の始域射影が普遍矢印の族であることを反転する。
規約：raw な円柱の射が一致する。
使われ方：slice の標準変換を比較の底の図式として回収する。 -/
lemma kanLeftCommaIdentityComparison_projection {K C : SSet.{u}} (δ : K ⟶ C) :
    (kanLeftCommaIdentityComparison δ).h ≫ kanLeftCommaProjection δ =
      (kanLeftCommaHomotopy δ).h := by
  have hv : (SerrePositivity.InfinityCategories.homotopyOpposite (SerrePositivity.InfinityCategories.F1B.unitCommaContraction (SSet.opFunctor.map δ))).h ≫
      SSet.opFunctor.map (unitCommaSource (SSet.opFunctor.map δ)) =
        (SerrePositivity.InfinityCategories.homotopyOpposite (unitCommaHomotopy (𝟙 (unitComma (SSet.opFunctor.map δ))))).h := by
    rw [← kanHomotopyOpposite_postcomp_h]
    dsimp only [SerrePositivity.InfinityCategories.homotopyOpposite, functorHomotopyPostcomp]
    rw [SerrePositivity.InfinityCategories.F1B.unitCommaContraction_source]
  change (SerrePositivity.InfinityCategories.homotopyOpposite (SerrePositivity.InfinityCategories.F1B.unitCommaContraction (SSet.opFunctor.map δ))).h ≫
    SSet.opFunctor.map (unitCommaSource (SSet.opFunctor.map δ)) ≫
      (SSet.opFunctorCompOpFunctorIso.app C).hom = _
  rw [← Category.assoc, hv]
  rfl

end SerrePositivity.InfinityCategories.F1B
