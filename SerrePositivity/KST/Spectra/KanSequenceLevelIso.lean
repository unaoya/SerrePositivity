module

public import SerrePositivity.KST.Spectra.KanSequenceCategory
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomotopyIsomorphism

/-!
概要：段ごとの点つき同型による Kan 列の構造射と Ω 条件の移送。
方針：随伴構造射を同型で共役し、uncurry して厳密な比較射を作る。
規約：段の同型を指定した実際の列を構成する。単射性は要求しない。
使われ方：BF 1978 §2、HA §1.4.2。通常の Tot の段への Ω 構造の移送。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.KanSequence

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : KanSequence.{u}) (Z : ℕ → PointedKanComplex.{u})
    (e : ∀ n, (Z n).space ≅ (X.level n).space)

/-- 概要：同型な各段へ随伴構造射を移して Kan 列を作る。
方針：段の同型、元の随伴構造射、次段の loop の逆同型を合成して uncurry する。
規約：各段は指定された Z の対象そのもの。
使われ方：HA §1.4.2、BF 1978 §2。end の構造を通常の Tot の段へ移す。 -/
def changeLevels : KanSequence.{u} where
  level := Z
  sigma n := uncurry ((e n).hom ≫ curry (X.sigma n) ≫
    (ihom PointedSimplicialSet.circle.{u}).map (e (n + 1)).inv)

/-- 概要：段の同型は移送した列から元の列への厳密な射を与える。
方針：curry した可換式で loop の逆同型と同型を相殺する。
規約：構造射は厳密に可換する。
使われ方：HA §1.4.2、BF 1978 §2。通常の Tot と BK end の比較。 -/
def changeLevelsProjection : Hom (changeLevels X Z e) X where
  app n := (e n).hom
  comm n := by
    apply (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (Z n).space (X.level (n + 1)).space).injective
    change curry (PointedSimplicialSet.circle.{u} ◁ (e n).hom ≫ X.sigma n) =
      curry (uncurry ((e n).hom ≫ curry (X.sigma n) ≫
        (ihom PointedSimplicialSet.circle.{u}).map (e (n + 1)).inv) ≫ (e (n + 1)).hom)
    rw [curry_natural_left, curry_natural_right, curry_uncurry,
      Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- 概要：段の同型で移送した列は元の列の Ω 条件を保つ。
方針：随伴構造射の前後の同型による全基点 π_* 同型を合成する。
規約：零次数を含む全基点の条件。
使われ方：HA §1.4.2、BF 1978 §2。通常の Tot の Kan Ω 列の構成。 -/
lemma changeLevels_omegaCondition (hX : X.OmegaCondition) :
    (changeLevels X Z e).OmegaCondition := by
  intro n
  let a : (Z n).space.right ≅ (X.level n).space.right :=
    PointedSimplicialSet.forget.mapIso (e n)
  let b : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X.level (n + 1)).space).right ≅ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (Z (n + 1)).space).right :=
    PointedSimplicialSet.forget.mapIso
      ((ihom PointedSimplicialSet.circle.{u}).mapIso (e (n + 1)).symm)
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso a).comp ((hX n).comp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso b))
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (X := (Z n).space.right)
    (Y := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (Z (n + 1)).space).right)
    (curry (uncurry ((e n).hom ≫ curry (X.sigma n) ≫
    (ihom PointedSimplicialSet.circle.{u}).map (e (n + 1)).inv))).right
  rw [curry_uncurry]
  exact h

end

end SerrePositivity.KST.Spectra.KanSequence
