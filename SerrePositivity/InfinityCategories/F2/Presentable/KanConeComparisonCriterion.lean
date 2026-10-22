module

public import SerrePositivity.InfinityCategories.F2.Presentable.WeightedCotensor
public import SerrePositivity.InfinityCategories.HomotopyLimits.GeneralOriginalCriterion
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanConeLimits
public import SerrePositivity.InfinityCategories.F1B.WeakWhitehead
public import SerrePositivity.InfinityCategories.Core.FunctorComposition

/-!
概要：Kan 複体の strict 錐の元の Bousfield–Kan 比較から native な極限性を得る。
方針：内部 Hom との交換により全表現可能 Hom の比較を回収し、N の全錐の判定を使う。
規約：比較の弱同値性は明示的な証明引数。形状の制約・Hom の strict 極限性は要求しない。
使われ方：μ-filtered な錐族の比較の保存を実際の Space の極限性へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable {I : Type u} [SmallCategory I]

/-- 元の Kan 錐の比較が弱同値なら、同じ coherent 錐は実際の ∞ 極限錐。 -/
lemma kanCone_isLimit_of_bousfieldKanComparison {F : I ⥤ KanObject.{u}} (c : Cone F)
    (hc : IsWeakHomotopyEquivalence (bousfieldKanConeComparison (kanObjectForget.mapCone c))) :
    IsLimitCone (strictCoherentCone c) := by
  have : KanComplex (kanObjectForget.mapCone c).pt :=
    inferInstanceAs (KanComplex c.pt.obj)
  have (i : I) : KanComplex ((F ⋙ kanObjectForget).obj i) :=
    inferInstanceAs (KanComplex (F.obj i).obj)
  have : KanComplex (bousfieldKanHolim (F ⋙ kanObjectForget)) :=
    bousfieldKanHolim_kanComplex _
  have hq := hc.isSimplicialHomotopyEquivalence.isQCatEquivalence
  apply (strictCoherentCone_isLimit_iff_general_representableComparison c).2
  intro X
  change IsSimplicialHomotopyEquivalence
    (@bousfieldKanConeComparison I _
      (F ⋙ (SimplicialCategory.sHomFunctor KanObject).obj (Opposite.op X))
      (((SimplicialCategory.sHomFunctor KanObject).obj (Opposite.op X)).mapCone c))
  rw [kanObjectHomFunctor_eq]
  change IsSimplicialHomotopyEquivalence
    (weightedConeComparison (bousfieldKanWeight I)
      ((ihom X.obj).mapCone (kanObjectForget.mapCone c)))
  rw [← weightedConeComparison_cotensor]
  have hMap := (hq.postcompose X.obj).isWeakHomotopyEquivalence
  have (i : I) : KanComplex (((F ⋙ kanObjectForget) ⋙ ihom X.obj).obj i) :=
    inferInstanceAs (KanComplex ((ihom X.obj).obj (F.obj i).obj))
  have : KanComplex
      (((Functor.whiskeringRight I SSet.{u} SSet.{u}).obj (ihom X.obj) ⋙
        weightedSectionsFunctor (bousfieldKanWeight I)).obj (F ⋙ kanObjectForget)) := by
    change KanComplex (bousfieldKanHolim ((F ⋙ kanObjectForget) ⋙ ihom X.obj))
    exact bousfieldKanHolim_kanComplex _
  have hIso := (isPrecompositionEquivalence_of_iso
    ((weightedSectionsCotensorIso (bousfieldKanWeight I) X.obj).app
      (F ⋙ kanObjectForget))).isWeakHomotopyEquivalence
  exact (hMap.comp hIso).isSimplicialHomotopyEquivalence

/-- native な極限錐の一点からの Hom を、元の Kan 複体の比較射へ自然に戻す。 -/
lemma bousfieldKanComparison_of_kanCone_isLimit {F : I ⥤ KanObject.{u}} (c : Cone F)
    (hc : IsLimitCone (strictCoherentCone c)) :
    IsWeakHomotopyEquivalence (bousfieldKanConeComparison (kanObjectForget.mapCone c)) := by
  let e := Functor.isoWhiskerLeft F pointKanObjectHomNatIso
  have hq := ((strictCoherentCone_isLimit_iff_general_representableComparison c).1 hc
    pointKanObject).isWeakHomotopyEquivalence
  have hn := weightedConeComparison_naturality (bousfieldKanWeight I)
    (simplicialHomCone c pointKanObject) (kanObjectForget.mapCone c)
    (pointKanObjectHomIso c.pt).hom e.hom (fun i ↦ by
      exact pointKanObjectHomNatIso.hom.naturality (c.π.app i))
  have he := (isPrecompositionEquivalence_of_iso
    ((weightedSectionsFunctor (bousfieldKanWeight I)).mapIso e)).isWeakHomotopyEquivalence
  apply (isPrecompositionEquivalence_of_iso
    (pointKanObjectHomIso c.pt)).isWeakHomotopyEquivalence.cancel_left
  change IsWeakHomotopyEquivalence ((pointKanObjectHomIso c.pt).hom ≫
    weightedConeComparison (bousfieldKanWeight I) (kanObjectForget.mapCone c))
  rw [hn]
  exact hq.comp he

/-- Kan 複体の任意の strict 錐の native な極限性は、元の比較射の弱同値性で検出できる。 -/
lemma kanCone_isLimit_iff_bousfieldKanComparison {F : I ⥤ KanObject.{u}} (c : Cone F) :
    IsLimitCone (strictCoherentCone c) ↔
      IsWeakHomotopyEquivalence (bousfieldKanConeComparison (kanObjectForget.mapCone c)) :=
  ⟨bousfieldKanComparison_of_kanCone_isLimit c, kanCone_isLimit_of_bousfieldKanComparison c⟩

end SerrePositivity.InfinityCategories.F2.Presentable
