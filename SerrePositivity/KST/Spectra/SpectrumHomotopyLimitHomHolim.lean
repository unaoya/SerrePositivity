module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitMappingEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedFunctor

/-!
概要：元の BF homotopy limit の豊穣 Hom と、元の豊穣 Hom 図式の Bousfield–Kan end の同値。
方針：厳密な Hom-end 交換の後、点つき end の忘却同型と実際の豊穣後合成の一致を使う。
規約：添字の有限性や Reedy 条件を要求しない。使われ方：一般形状の γ3 の錐比較への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance homHolimSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance homHolimHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y
variable {I : Type u} [SmallCategory I]
local instance homHolimCoefficientKan (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) (i : I) :
    KanComplex ((((D ⋙ forgetToKan) ⋙ RawSpectrumMapping.pointedFunctor X).obj i).right) :=
  RawSpectrumMapping.pointedSpace_kanComplex X (D.obj i).toKanSequence
local instance homHolimDiagramKan (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) (i : I) :
    KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X).obj i) := mappingSpace_kanComplex X (D.obj i)
local instance homHolimEndKan (X : OmegaSpectrum.{u}) (D : I ⥤ OmegaSpectrum.{u}) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X)

/-- 一般の Kan 列の点つき Hom を忘れると、元の BF 豊穣 Hom の図式と厳密に同型。 -/
def rawSimplicialHomDiagramIso (X : OmegaSpectrum.{u}) (D : I ⥤ OmegaSpectrum.{u}) :
    (((D ⋙ forgetToKan) ⋙ RawSpectrumMapping.pointedFunctor X) ⋙ PointedSimplicialSet.forget) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {i j} f ↦ by
    change RawSpectrumMapping.post X
        (⟨(D.map f).app, (D.map f).comm⟩ : KanSequence.Hom (D.obj i).toKanSequence
          (D.obj j).toKanSequence) ≫ 𝟙 (mappingSpace X (D.obj j)) =
      𝟙 (mappingSpace X (D.obj i)) ≫
        ((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X)).map (D.map f)
    exact (Category.comp_id (RawSpectrumMapping.post X
      (⟨(D.map f).app, (D.map f).comm⟩ : KanSequence.Hom (D.obj i).toKanSequence
        (D.obj j).toKanSequence))).trans
      ((RawSpectrumMapping.post_spectrum X (D.map f)).trans (Category.id_comp _).symm))

/-- 点つき Hom の homotopy end を忘れると、元の豊穣 Hom の Bousfield–Kan end と同型。 -/
def homotopyLimitHomEndUnderlyingIso (X : OmegaSpectrum.{u}) (D : I ⥤ OmegaSpectrum.{u}) :
    (PointedWeightedEnd.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
      ((D ⋙ forgetToKan) ⋙ RawSpectrumMapping.pointedFunctor X)).right ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X) :=
  PointedWeightedEnd.underlyingIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
      ((D ⋙ forgetToKan) ⋙ RawSpectrumMapping.pointedFunctor X) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)).mapIso (rawSimplicialHomDiagramIso X D)

/-- 任意の小さい通常図式の BF homotopy limit は、実際の豊穣 Hom を homotopy end に送る。 -/
def homotopyLimitHomHolimEquivalence (X : OmegaSpectrum.{u}) (D : I ⥤ OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (mappingSpace X (homotopyLimit D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X)) :=
  (homotopyLimitMappingEquivalence X D).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (homotopyLimitHomEndUnderlyingIso X D))

/-- 指定した順射は BF 比較と、元の豊穣 Hom 図式への忘却同型の合成。 -/
lemma homotopyLimitHomHolimEquivalence_hom (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) :
    (homotopyLimitHomHolimEquivalence X D).hom =
      (homotopyLimitMappingEquivalence X D).hom ≫ (homotopyLimitHomEndUnderlyingIso X D).hom := rfl

/-- 指定した Hom 比較は、単体的ホモトピー逆を持つ実際の射。 -/
lemma homotopyLimitHomHolim_homotopyEquivalence (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (homotopyLimitHomHolimEquivalence X D).hom :=
  (homotopyLimitHomHolimEquivalence X D).isQCatEquivalence.isSimplicialHomotopyEquivalence

end SerrePositivity.KST.Spectra.OmegaSpectrum
