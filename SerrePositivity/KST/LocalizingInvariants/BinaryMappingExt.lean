module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumBinaryMaps
public import SerrePositivity.KST.LocalizingInvariants.SpectrumComponentClass

/-!
概要：元の BF 二項積への h Sp の射は、両射影との合成で決まる。
方針：実豊穣 Hom の極限で二つの Hom の辺を同時に持ち上げる。
規約：整数 π の一致による射の等式とは区別する。使われ方：分裂比較の射影との整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
open SpectrumMappingAcyclic
namespace SerrePositivity.KST.LocalizingInvariants.Binary

local instance binaryMappingSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {A X Y : OmegaSpectrum.{u}}

def familyCone {T : SSet.{u}} (f : T ⟶ mappingSpace A X) (g : T ⟶ mappingSpace A Y) :
    Cone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumBinaryProductDiagram X Y) A) where
  pt := T
  π := Discrete.natTrans (by
    rintro ⟨⟨i⟩⟩
    cases i
    · exact f
    · exact g)

def familyLift {T : SSet.{u}} (f : T ⟶ mappingSpace A X) (g : T ⟶ mappingSpace A Y) :
    T ⟶ mappingSpace A (obj X Y) :=
  (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumBinaryProductCone_hom_isLimit X Y A).lift (familyCone f g)

lemma familyLift_fst {T : SSet.{u}} (f : T ⟶ mappingSpace A X) (g : T ⟶ mappingSpace A Y) :
    familyLift f g ≫ post A (fst X Y) = f :=
  (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumBinaryProductCone_hom_isLimit X Y A).fac (familyCone f g) ⟨⟨WalkingPair.left⟩⟩

lemma familyLift_snd {T : SSet.{u}} (f : T ⟶ mappingSpace A X) (g : T ⟶ mappingSpace A Y) :
    familyLift f g ≫ post A (snd X Y) = g :=
  (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumBinaryProductCone_hom_isLimit X Y A).fac (familyCone f g) ⟨⟨WalkingPair.right⟩⟩

lemma mapping_vertex_ext {v w : (mappingSpace A (obj X Y)) _⦋0⦌}
    (hfst : (post A (fst X Y)).app _ v = (post A (fst X Y)).app _ w)
    (hsnd : (post A (snd X Y)).app _ v = (post A (snd X Y)).app _ w) : v = w := by
  apply SSet.yonedaEquiv.symm.injective
  apply (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumBinaryProductCone_hom_isLimit X Y A).hom_ext
  rintro ⟨⟨i⟩⟩
  cases i
  · change SSet.yonedaEquiv.symm v ≫ post A (fst X Y) =
      SSet.yonedaEquiv.symm w ≫ post A (fst X Y)
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, hfst]
  · change SSet.yonedaEquiv.symm v ≫ post A (snd X Y) =
      SSet.yonedaEquiv.symm w ≫ post A (snd X Y)
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, hsnd]

/-- 両射影で一致する Hom の成分は、元の全 Hom の成分として一致する。 -/
lemma component_ext (f g : A ⟶ obj X Y)
    (hfst : component (f ≫ fst X Y) = component (g ≫ fst X Y))
    (hsnd : component (f ≫ snd X Y) = component (g ≫ snd X Y)) : component f = component g := by
  obtain ⟨ef⟩ := nonempty_edge_of_piZero_eq hfst
  obtain ⟨eg⟩ := nonempty_edge_of_piZero_eq hsnd
  let L := familyLift (CartesianMonoidalCategory.fst (mappingSpace A X) (mappingSpace A Y))
    (CartesianMonoidalCategory.snd (mappingSpace A X) (mappingSpace A Y))
  have hv (a : A ⟶ obj X Y) :
      L.app (Opposite.op ⦋0⦌) (vertexOfHom (a ≫ fst X Y), vertexOfHom (a ≫ snd X Y)) =
        vertexOfHom a := by
    apply mapping_vertex_ext
    · have h := CategoryTheory.types_congr_hom (NatTrans.congr_app
        (familyLift_fst (CartesianMonoidalCategory.fst (mappingSpace A X) (mappingSpace A Y))
          (CartesianMonoidalCategory.snd (mappingSpace A X) (mappingSpace A Y))) (Opposite.op ⦋0⦌))
        (vertexOfHom (a ≫ fst X Y), vertexOfHom (a ≫ snd X Y))
      exact h.trans (post_vertex a (fst X Y)).symm
    · have h := CategoryTheory.types_congr_hom (NatTrans.congr_app
        (familyLift_snd (CartesianMonoidalCategory.fst (mappingSpace A X) (mappingSpace A Y))
          (CartesianMonoidalCategory.snd (mappingSpace A X) (mappingSpace A Y))) (Opposite.op ⦋0⦌))
        (vertexOfHom (a ≫ fst X Y), vertexOfHom (a ≫ snd X Y))
      exact h.trans (post_vertex a (snd X Y)).symm
  let e := SSet.Edge.ofTruncated (X := mappingSpace A (obj X Y))
    ((ef.toTruncated.tensor eg.toTruncated).map ((truncation 2).map L))
  exact π₀.sound (e.ofEq (hv f) (hv g))

lemma hom_ext (f g : A ⟶ obj X Y)
    (hfst : SpectrumHo.hom f ≫ SpectrumHo.hom (fst X Y) =
      SpectrumHo.hom g ≫ SpectrumHo.hom (fst X Y))
    (hsnd : SpectrumHo.hom f ≫ SpectrumHo.hom (snd X Y) =
      SpectrumHo.hom g ≫ SpectrumHo.hom (snd X Y)) : SpectrumHo.hom f = SpectrumHo.hom g := by
  have hf := SpectrumHo.component_eq_of_hom_eq (f ≫ fst X Y) (g ≫ fst X Y)
    ((SpectrumHo.hom_comp _ _).trans (hfst.trans (SpectrumHo.hom_comp _ _).symm))
  have hg := SpectrumHo.component_eq_of_hom_eq (f ≫ snd X Y) (g ≫ snd X Y)
    ((SpectrumHo.hom_comp _ _).trans (hsnd.trans (SpectrumHo.hom_comp _ _).symm))
  exact SpectrumHo.hom_eq_of_component_eq _ _ (component_ext f g hf hg)

end SerrePositivity.KST.LocalizingInvariants.Binary
