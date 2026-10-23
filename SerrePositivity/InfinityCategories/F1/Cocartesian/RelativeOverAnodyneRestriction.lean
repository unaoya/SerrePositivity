module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.RelativeRestriction
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorOverPrecomposition
public import SerrePositivity.InfinityCategories.F1.InnerAnodyneReplacement
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianInnerAnodynePullback

/-!
概要：元の底上の単射な同値と、inner anodyne な底変換による相対 Hom の自明 Kan 制限。
方針：cocartesian 標的の相対制限と、始域射影に沿う inner anodyne の逆像の同値性を結ぶ。
規約：指定辺の保存条件は別途反映を確認してから課す。
使われ方：高次単体の元の cocartesian Hom をその部分図式へ制限する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 元の底上の単射な同値による、cocartesian 標的への全相対 Hom の制限は自明 Kan。 -/
lemma relativeFunctorOverPre_trivialKanFibration_of_cocartesian
    {E B : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [CocartesianFibration q]
    {a b : Over B} (i : a ⟶ b) [Mono i.left] (hi : IsPrecompositionEquivalence i.left) :
    TrivialKanFibration (relativeFunctorOverPre q i) := by
  have h (d : a.left ⟶ B) (hd : i.left ≫ b.hom = d) :
      TrivialKanFibration (relativeFunctorOverPre q
        (Over.homMk (U := Over.mk d) (V := b) i.left hd)) := by
    subst d
    exact relativeFunctorPre_trivialKanFibration_of_cocartesian q b.hom i.left hi
  exact h a.hom i.w

/-- cocartesian な始域射影に沿う、inner anodyne な底の包含の逆像も単射な前合成同値。 -/
lemma cocartesianPullback_snd_isPrecompositionEquivalence_of_innerAnodyne
    {E A B : SSet.{u}} (p : E ⟶ B) [CocartesianFibration p]
    (i : A ⟶ B) (hi : innerAnodyneExtensions i) :
    IsPrecompositionEquivalence (pullback.snd i p) := by
  have h := (isPrecompositionEquivalence_of_iso (pullbackSymmetry i p)).comp
    (kanCocartesianFibration_pullback_innerAnodyne_isPrecompositionEquivalence p i hi)
  rwa [pullbackSymmetry_hom_comp_fst] at h

/-- inner anodyne な底への逆像制限は、元の全相対 Hom の自明 Kan fibration。 -/
lemma relativeFunctorPre_pullback_trivialKanFibration_of_cocartesian
    {E F A B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]
    (i : A ⟶ B) (hi : innerAnodyneExtensions i) :
    TrivialKanFibration (relativeFunctorPre q p (pullback.snd i p)) := by
  letI : Mono i := mono_of_innerAnodyne i hi
  exact relativeFunctorPre_trivialKanFibration_of_cocartesian q p _
    (cocartesianPullback_snd_isPrecompositionEquivalence_of_innerAnodyne p i hi)

end SerrePositivity.InfinityCategories
