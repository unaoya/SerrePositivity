module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.StrictSimplicialTransformation

/-! # 元の成分を回収する厳密自然変換の全 Hom の前後合成
概要：厳密豊穣自然変換の指定通常成分が、全 Hom の前後合成に自然であることを示す。
方針：元の単位次数の自然性を全単体で評価し、成分の回収式を適用する。
規約：通常の頂点だけの自然性には制限しない。使われ方：span 全体への end 豊穣作用。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet

/-- 指定成分を持つ厳密自然変換は、全 Hom の同じ前後合成を厳密に可換にする。 -/
lemma strictSimplicialTransformation_whisker
    {C : Type v} {D : Type w} [EnrichedCategory SSet.{u} C]
    [Category.{u} D] [SimplicialCategory D]
    (F G : EnrichedFunctor SSet.{u} C D)
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (τ : ∀ X, F.obj X ⟶ G.obj X) (hτ : ∀ X, η.app X = eHomEquiv SSet (τ X)) (X Y : C) :
    F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (τ Y) =
      G.map X Y ≫ eHomWhiskerRight SSet (τ X) (G.obj Y) := by
  ext n p
  have h := types_congr_hom (NatTrans.congr_app (η.naturality X Y) n) (PUnit.unit, p)
  change (eComp SSet (F.obj X) (F.obj Y) (G.obj Y)).app n
    ((F.map X Y).app n p, (η.app Y).app n PUnit.unit) =
    (eComp SSet (F.obj X) (G.obj X) (G.obj Y)).app n
      ((η.app X).app n PUnit.unit, (G.map X Y).app n p) at h
  rw [hτ X, hτ Y] at h
  exact h

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.strictSimplicialTransformation_whisker := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformation_whisker
