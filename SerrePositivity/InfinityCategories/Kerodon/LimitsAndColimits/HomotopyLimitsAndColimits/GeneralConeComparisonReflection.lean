module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanHomotopyInvariance
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ConeComparisonReflection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEdgewiseFunctor

/-!
概要：任意の小圏上の Kan な錐の Bousfield–Kan 比較の同値性は係数の反転で変わらない。
方針：自然な edgewise 解像の左右の射影と end の誘導射で二つの可換正方形を作る。
規約：厳密極限の Kan 性・標準比較の同値性・遷移の fibration 性を仮定しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、元の非反転 q_x の一般形状の極限判定。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- 概要：任意の単体集合の図式の edgewise 解像から元の図式への自然変換。
方針：右端射影の自然性を各構造射へ適用する。
規約：定義には Kan 性を要求しない。
使われ方：HTT 4.2.4.1、非反転の係数への比較。 -/
def diagramEdgewiseRight (H : I ⥤ SSet.{u}) : H ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor ⟶ H where
  app i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (H.obj i)
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_naturality (H.map f)

/-- 概要：edgewise 解像から係数を反転した図式への自然変換。
方針：左端射影の自然性を各構造射へ適用する。
規約：添字の射の向きは変えず、値の単体順序だけを反転する。
使われ方：HTT 4.2.4.1、反転した係数への比較。 -/
def diagramEdgewiseLeft (H : I ⥤ SSet.{u}) :
    H ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor ⟶ H ⋙ SSet.opFunctor where
  app i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft (H.obj i)
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft_naturality (H.map f)

/-- 概要：edgewise な錐の比較と元の錐の比較は右射影で厳密に可換。
方針：錐の比較の一般の自然性に右端射影の自然性を渡す。
規約：Kan 性・極限性は不要。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、元の q の同値性の消去。 -/
lemma bousfieldKanConeComparison_edgewiseRight {H : I ⥤ SSet.{u}} (c : Cone H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight c.pt ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.mapCone c) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (diagramEdgewiseRight H) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.mapCone c) c (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight c.pt) (diagramEdgewiseRight H)
  intro i
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_naturality (c.π.app i)).symm

/-- 概要：edgewise な錐の比較と反転係数の錐の比較は左射影で厳密に可換。
方針：錐の比較の一般の自然性に左端射影の自然性を渡す。
規約：Kan 性・極限性は不要。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、反転した q′ の同値性の消去。 -/
lemma bousfieldKanConeComparison_edgewiseLeft {H : I ⥤ SSet.{u}} (c : Cone H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft c.pt ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (SSet.opFunctor.mapCone c) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.mapCone c) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (diagramEdgewiseLeft H) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.mapCone c) (SSet.opFunctor.mapCone c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft c.pt) (diagramEdgewiseLeft H)
  intro i
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft_naturality (c.π.app i)).symm

/-- 概要：Kan 値図式の edgewise な係数の右比較は Bousfield–Kan end でも同値。
方針：各成分の trivial Kan fibration 性を end の同値不変性へ渡す。
規約：添字の形状や遷移の fibration 性は要求しない。
使われ方：HTT 4.2.4.1、共通 end から元の end への実際の比較。 -/
lemma bousfieldKanEdgewiseRight_homotopyEquivalence (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (diagramEdgewiseRight H)) := by
  have : ∀ i, KanComplex ((H ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (H.obj i)))
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanMap_homotopyEquivalence
  intro i
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_trivialKanFibration (H.obj i)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (H.obj i))
  exact h.isSimplicialHomotopyEquivalence

/-- 概要：Kan 値図式の edgewise な係数の左比較も Bousfield–Kan end で同値。
方針：各成分の左射影の trivial Kan fibration 性を end の同値不変性へ渡す。
規約：標的は値を反転した図式の実際の end。
使われ方：HTT 4.2.4.1、共通 end から反転 end への比較。 -/
lemma bousfieldKanEdgewiseLeft_homotopyEquivalence (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (diagramEdgewiseLeft H)) := by
  have : ∀ i, KanComplex ((H ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (H.obj i)))
  have : ∀ i, KanComplex ((H ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (H.obj i).op)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanMap_homotopyEquivalence
  intro i
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft_trivialKanFibration (H.obj i)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft (H.obj i))
  exact h.isSimplicialHomotopyEquivalence

/-- 概要：任意の小圏上の Kan な錐の元の比較と反転比較の同値性は一致する。
方針：edgewise 共通解像の左右の可換正方形で頂点と end の四つの同値を消去する。
規約：錐の厳密極限性・厳密極限の Kan 性・標準比較の同値性を仮定しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、γ3b の元の q_x の一般形状の判定。 -/
lemma bousfieldKanConeComparison_reflection_general_iff
    {H : I ⥤ SSet.{u}} (c : Cone H) [KanComplex c.pt] [∀ i, KanComplex (H.obj i)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (SSet.opFunctor.mapCone c)) := by
  have : ∀ i, KanComplex ((H ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (H.obj i)))
  have : ∀ i, KanComplex ((H ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (H.obj i).op)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex H
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (H ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (H ⋙ SSet.opFunctor)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_trivialKanFibration c.pt
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft_trivialKanFibration c.pt
  have hr₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight c.pt)
  have hl₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft c.pt)
  have hr := hr₀.isSimplicialHomotopyEquivalence
  have hl := hl₀.isSimplicialHomotopyEquivalence
  have hR := bousfieldKanEdgewiseRight_homotopyEquivalence H
  have hL := bousfieldKanEdgewiseLeft_homotopyEquivalence H
  constructor
  · intro h
    have he := hr.comp h
    rw [bousfieldKanConeComparison_edgewiseRight] at he
    have hE := hR.cancel_right he
    have ht := hE.comp hL
    rw [← bousfieldKanConeComparison_edgewiseLeft] at ht
    exact hl.cancel_left ht
  · intro h
    have he := hl.comp h
    rw [bousfieldKanConeComparison_edgewiseLeft] at he
    have hE := hL.cancel_right he
    have ht := hE.comp hR
    rw [← bousfieldKanConeComparison_edgewiseRight] at ht
    exact hr.cancel_left ht

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
