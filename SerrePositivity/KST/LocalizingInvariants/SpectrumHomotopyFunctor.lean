module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomotopyClass

/-!
概要：Sp のホモトピー圏から全整数次数の可換群への実関手。
方針：辺の代表を BF 射へ戻し、元の射の類による不変性で選択を消す。
規約：対象も元の Sp の頂点から回収する。使われ方：K-5 の fiber 長完全列の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumHo

local instance homotopyFunctorSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance homotopyFunctorHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y

/-- ホモトピー圏の任意の射を、元の端点の BF 射で表す。 -/
lemma exists_representative {X Y : OmegaSpectrum.{u}} (m : obj X ⟶ obj Y) :
    ∃ f : X ⟶ Y, hom f = m := by
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) m
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom (SSet.Edge.ofTruncated e)
  refine ⟨a, ?_⟩
  have ha := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_hom (SSet.Edge.ofTruncated e)
  exact (congrArg (fun k ↦ SSet.Truncated.HomotopyCategory.homMk
    (SSet.Edge.toTruncated k)) ha).trans he

def representative {X Y : OmegaSpectrum.{u}} (m : obj X ⟶ obj Y) : X ⟶ Y :=
  Classical.choose (exists_representative m)

lemma hom_representative {X Y : OmegaSpectrum.{u}} (m : obj X ⟶ obj Y) :
    hom (representative m) = m := Classical.choose_spec (exists_representative m)

/-- 元の Sp の任意の頂点を BF 対象へ戻す。 -/
def spectrum (x : hoFunctor.obj Sp.{u}) : OmegaSpectrum.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject x.as.as

def spectrumIso (x : hoFunctor.obj Sp.{u}) : obj (spectrum x) ≅ x :=
  eqToIso (SSet.Truncated.HomotopyCategory.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object x.as.as))

def normalize {x y : hoFunctor.obj Sp.{u}} (m : x ⟶ y) :
    obj (spectrum x) ⟶ obj (spectrum y) := (spectrumIso x).hom ≫ m ≫ (spectrumIso y).inv

lemma normalize_id (x : hoFunctor.obj Sp.{u}) : normalize (𝟙 x) = 𝟙 _ := by
  simp only [normalize, Category.id_comp, Iso.hom_inv_id]

lemma normalize_comp {x y z : hoFunctor.obj Sp.{u}} (f : x ⟶ y) (g : y ⟶ z) :
    normalize (f ≫ g) = normalize f ≫ normalize g := by
  simp only [normalize, Category.assoc, Iso.inv_hom_id_assoc]

/-- 任意のホモトピー圏の射による整数 π の作用。 -/
def piMap {x y : hoFunctor.obj Sp.{u}} (m : x ⟶ y) (j : ℤ) :
    homotopyGroup (spectrum x) j →* homotopyGroup (spectrum y) j :=
  homotopyMap (representative (normalize m)) j

lemma piMap_id (x : hoFunctor.obj Sp.{u}) (j : ℤ) : piMap (𝟙 x) j = MonoidHom.id _ := by
  have h : hom (representative (normalize (𝟙 x))) = hom (𝟙 (spectrum x)) := by
    rw [hom_representative, normalize_id, hom_id]
  exact (homotopyMap_eq_of_hom_eq _ _ h j).trans (homotopyMap_id _ j)

lemma piMap_comp {x y z : hoFunctor.obj Sp.{u}} (f : x ⟶ y) (g : y ⟶ z) (j : ℤ) :
    piMap (f ≫ g) j = (piMap g j).comp (piMap f j) := by
  have h : hom (representative (normalize (f ≫ g))) =
      hom (representative (normalize f) ≫ representative (normalize g)) := by
    rw [hom_comp, hom_representative, hom_representative, hom_representative, normalize_comp]
  exact (homotopyMap_eq_of_hom_eq _ _ h j).trans (homotopyMap_comp _ _ j)

/-- Sp の実際のホモトピー圏上の整数 π 関手。 -/
def piFunctor (j : ℤ) : hoFunctor.obj Sp.{u} ⥤ CommGrpCat.{u} where
  obj x := CommGrpCat.of (homotopyGroup (spectrum x) j)
  map m := CommGrpCat.ofHom (piMap m j)
  map_id x := congrArg CommGrpCat.ofHom (piMap_id x j)
  map_comp f g := congrArg CommGrpCat.ofHom (piMap_comp f g j)

end SerrePositivity.KST.LocalizingInvariants.SpectrumHo
