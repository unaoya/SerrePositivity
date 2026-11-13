module
public import SerrePositivity.KST.SConstruction.GappedCofibers
public import SerrePositivity.KST.SConstruction.FunctorCofiberPreservation

/-! # S 構成の構造射の cofiber 保存
概要：S_n の面・退化と保存条件を持つ射による後合成は cofiber を保つ。
方針：包含後の cofiber 性を Ar の各点で判定し、前合成・後合成の評価式を使う。
規約：零角つき正方形に対する保存。使われ方：反復 S• の関手性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：S_n の単体作用と Ar の評価は可換。
方針：包含後の前合成の式と評価の自然性を使う。
規約：quasicategory 性は不要。使われ方：cofiber 性の評価。 -/
lemma sMap_gapped_evaluate {m n : ℕ} (C : SSet.{u})
    (θ : Fin (m + 1) →o Fin (n + 1)) (a : (arNerve m) _⦋0⦌) :
    sMap C θ ≫ (gappedSubcomplex m C).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a =
      (gappedSubcomplex n C).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((arNerveMap θ).app (Opposite.op ⦋0⦌) a) := by
  rw [← Category.assoc, sMap_ι, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]

/-- 概要：S_n の後合成と Ar の評価は可換。
方針：包含後の後合成の式と内部 Hom の評価を使う。
規約：保存条件以外に仮定は不要。使われ方：後合成の cofiber 保存。 -/
lemma sPostcomp_gapped_evaluate (n : ℕ) {C D : SSet.{u}}
    (f : C ⟶ D) (hf : PreservesSConstructionData f) (a : (arNerve n) _⦋0⦌) :
    sPostcomp n f hf ≫ (gappedSubcomplex n D).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a =
      (gappedSubcomplex n C).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a ≫ f := by
  rw [← Category.assoc, sPostcomp_ι, Category.assoc, ihom_postcomp_evaluate]

/-- 概要：S_n の単体作用で零角つき正方形を写す。
方針：面・退化写像の零対象保存を使う。
規約：C は零対象を持つ quasicategory。使われ方：cofiber 保存の記述。 -/
def sMapZeroTriangle {m n : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C]
    (θ : Fin (m + 1) →o Fin (n + 1)) (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle (sConstruction n C)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle (sConstruction m C) :=
  ⟨t.square ≫ sMap C θ, sMap_isZeroVertex θ t.zero_corner⟩

/-- 概要：S_n の後合成で零角つき正方形を写す。
方針：後合成写像の零対象保存を使う。
規約：chosen zero の一致は不要。使われ方：cofiber 保存の記述。 -/
def sPostcompZeroTriangle {n : ℕ} {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] (f : C ⟶ D) (hf : PreservesSConstructionData f)
    (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle (sConstruction n C)) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle (sConstruction n D) :=
  ⟨t.square ≫ sPostcomp n f hf, sPostcomp_isZeroVertex n f hf t.zero_corner⟩

/-- 概要：S_n の全ての面・退化写像は cofiber を保存する。
方針：Ar の各点での cofiber 性を添字の像へ制限して判定する。
規約：C の安定性だけを仮定する。使われ方：多単体的反復の各構造射。 -/
lemma sMap_preserves_cofiber {m n : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (θ : Fin (m + 1) →o Fin (n + 1)) (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle (sConstruction n C))
    (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence (sMapZeroTriangle θ t) := by
  apply (gappedInclusion_cofiber_iff_pointwise (sMapZeroTriangle θ t)).2
  intro a
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((t.square ≫ sMap C θ) ≫ (gappedSubcomplex m C).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a)
  rw [Category.assoc, sMap_gapped_evaluate]
  exact (gappedInclusion_cofiber_iff_pointwise t).1 ht _

/-- 概要：保存条件を持つ射の S_n への後合成は cofiber を保存する。
方針：元の cofiber を各点で評価し、保存後に S_n 内の普遍性へ戻す。
規約：両端は安定な quasicategory。使われ方：反復 K 理論の関手性。 -/
lemma sPostcomp_preserves_cofiber {n : ℕ} {C D : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [Quasicategory D] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable D]
    (f : C ⟶ D) (hf : PreservesSConstructionData f) (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle (sConstruction n C))
    (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence (sPostcompZeroTriangle f hf t) := by
  apply (gappedInclusion_cofiber_iff_pointwise (sPostcompZeroTriangle f hf t)).2
  intro a
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((t.square ≫ sPostcomp n f hf) ≫ (gappedSubcomplex n D).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a)
  rw [Category.assoc, sPostcomp_gapped_evaluate, ← Category.assoc, ← Category.assoc]
  exact hf.2 _ ((gappedInclusion_cofiber_iff_pointwise t).1 ht a)

end SerrePositivity.KST.SConstruction
