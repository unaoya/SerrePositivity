module

public import SerrePositivity.KST.Spectra.EdgewiseTensor

/-!
概要：パラメータ付き係数自然変換の edgewise 化と両端の可換式。
方針：テンソル比較の自然性と、左右射影の自然性を合成する。
規約：係数もパラメータも全単体を保持する。使われ方：Hom end の全パラメータ反転比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.EdgewiseTensor

variable {I : Type u} [SmallCategory I]
/-- 係数とパラメータを同時に edgewise 化した実際の係数自然変換。 -/
def parameterDiagram {H E : I ⥤ SSet.{u}} {B : SSet.{u}}
    (η : H ⋙ tensorRight B ⟶ E) :
    (H ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor) ⋙ tensorRight (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision B) ⟶
      E ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor where
  app i := map (H.obj i) B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (η.app i)
  naturality i j f := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (H.map f) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision B ≫
      map (H.obj j) B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (η.app j) =
      (map (H.obj i) B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (η.app i)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (E.map f)
    have hn := natural (H.map f) (𝟙 B)
    have hid : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (𝟙 B) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision B) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.map_id B
    rw [hid] at hn
    simp only [tensorHom_id] at hn
    rw [← Category.assoc, hn, Category.assoc]
    have hη := η.naturality f
    change H.map f ▷ B ≫ η.app j = η.app i ≫ E.map f at hη
    have he := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap hη
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.map (H.map f ▷ B ≫ η.app j) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.map (η.app i ≫ E.map f) at he
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.map_comp] at he
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (H.map f ▷ B) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (η.app j) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (η.app i) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (E.map f) at he
    rw [he, Category.assoc]

/-- 係数の全パラメータ作用は、係数とパラメータの右射影と可換。 -/
lemma parameterDiagram_right {H E : I ⥤ SSet.{u}} {B : SSet.{u}}
    (η : H ⋙ tensorRight B ⟶ E) (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (H.obj i) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight B) ≫ η.app i =
      (parameterDiagram η).app i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (E.obj i) := by
  change _ = (map (H.obj i) B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (η.app i)) ≫ _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_naturality, ← Category.assoc, right]

/-- 係数の全パラメータ作用は、係数とパラメータの左射影と可換。 -/
lemma parameterDiagram_left {H E : I ⥤ SSet.{u}} {B : SSet.{u}}
    (η : H ⋙ tensorRight B ⟶ E) (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft (H.obj i) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft B) ≫
        (Functor.Monoidal.μIso SSet.opFunctor (H.obj i) B).hom ≫
          SSet.opFunctor.map (η.app i) =
      (parameterDiagram η).app i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft (E.obj i) := by
  change _ = (map (H.obj i) B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (η.app i)) ≫ _
  conv_rhs => rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft_naturality, ← Category.assoc, left]
  simp only [Category.assoc]


end SerrePositivity.KST.Spectra.EdgewiseTensor
