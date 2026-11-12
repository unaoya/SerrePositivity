module
public import SerrePositivity.KST.SConstruction.MonicKPrismSpecifiedFamilies
public import SerrePositivity.KST.SConstruction.KOmegaSpectrum
public import SerrePositivity.KST.Spectra.RawSpectrumMapping

/-! # 元の K prism を指定境界付きの段の族の厳密化の入力にする
概要：元の単射源の全段の族と、構造射の全実適合円柱を既存の raw 写像空間の型で供給する。
方針：定数段族の二つの構造合成を元の二合成へ厳密に同定し、同じ実円柱を使う。
規約：指定境界は元の適合区間を回収し、定数境界の仮定は加えない。
使われ方：指定補正列・射影 trace を保持する全段の厳密化への具体的入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.PointedMapping SerrePositivity.InfinityCategories
open scoped Simplicial

/-- raw な段の境界比較は、元の頂点で suspension と標的構造射の合成を回収する。 -/
lemma rawSequenceStep_familyVertex (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) (n : ℕ)
    (f : (X.level n).space ⟶ (Y.level n).space) :
    (RawSpectrumMapping.step X Y n).app (Opposite.op ⦋0⦌) (familyVertex f) =
      familyVertex (PointedSimplicialSet.circle.{u} ◁ f ≫ Y.sigma n) := by
  simp only [familyVertex_eq_pointedHomVertex]
  change (PointedObject.basedHomMap _ (Y.sigma n)).right.app _
    ((suspensionHom _ _).right.app _ (pointedHomVertexEquiv _ _ f)) = _
  rw [pointedHomVertexEquiv_suspension, pointedHomVertexEquiv_post]

/-- 元の単射源の各段の写像を、全精密化の共通パラメータ上の族として表示する。 -/
def monicKPrismRawLevelFamily {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⟶
      (PointedObject.basedHom ((kOmegaSpectrum (F.obj x)).level r).space
        ((kKanSequence (F.obj y)).level r).space).right :=
  SSet.const (familyVertex (monicKToRawLevelMap (F.map f) r))

/-- 元の全段の適合円柱を、raw な段の族の二合成の間の同じ実円柱として供給する。 -/
def monicKPrismRawSequenceCompatibility {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    SSet.Homotopy
      (monicKPrismRawLevelFamily (r + 1) F f ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma r)
          ((kKanSequence (F.obj y)).level (r + 1)).space)
      (monicKPrismRawLevelFamily r F f ≫
        RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj y)) r) := by
  let H := monicKPrismSpecifiedCompatibilityFamily r F f
  have hs : monicKPrismRawLevelFamily (r + 1) F f ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma r)
          ((kKanSequence (F.obj y)).level (r + 1)).space =
      SSet.const (familyVertex ((monicKKanSequence (F.obj x)).sigma r ≫
        monicKToRawLevelMap (F.map f) (r + 1))) := by
    rw [monicKPrismRawLevelFamily, SSet.const_comp]
    exact congrArg (SSet.const (X := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)))
      (familyVertex_pre ((monicKKanSequence (F.obj x)).sigma r)
        (monicKToRawLevelMap (F.map f) (r + 1)))
  have ht : monicKPrismRawLevelFamily r F f ≫
        RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj y)) r =
      SSet.const (familyVertex (PointedSimplicialSet.circle.{u} ◁ monicKToRawLevelMap (F.map f) r ≫
        (kKanSequence (F.obj y)).sigma r)) := by
    rw [monicKPrismRawLevelFamily, SSet.const_comp, rawSequenceStep_familyVertex]
  exact
    { h := H.h
      h₀ := H.h₀.trans hs.symm
      h₁ := H.h₁.trans ht.symm
      rel := H.rel }

/-- raw 写像空間の入力として表示しても、元の全時刻の適合円柱は変わらない。 -/
lemma monicKPrismRawSequenceCompatibility_h {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (monicKPrismRawSequenceCompatibility r F f).h =
      (monicKPrismSpecifiedCompatibilityFamily r F f).h := rfl

/-- 厳密化の具体的入力の指定頂点で、元の単射源の適合区間を厳密に回収する。 -/
lemma monicKPrismRawSequenceCompatibility_boundary {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) ▷ (Δ[1] : SSet.{u})) ≫
      (monicKPrismRawSequenceCompatibility r F f).h =
        snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
          SSet.yonedaEquiv.symm (monicKPrismCompatibilityEdge r F f).edge :=
  monicKPrismSpecifiedCompatibilityFamily_boundary r F f

end SerrePositivity.KST.SConstruction
