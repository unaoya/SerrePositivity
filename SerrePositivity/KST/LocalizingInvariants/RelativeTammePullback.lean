module

public import SerrePositivity.KST.LocalizingInvariants.RelativeVerdierPullback
public import SerrePositivity.KST.LocalizingInvariants.BinaryProductCospanNormalized

/-!
概要：S 内の比較長方形とその E 像の積表示から、元の四辺を持つ d8 の pullback を得る。
方針：相対 Verdier 性から実 pullback を導き、全図式同型で積表示へ移して既存の正規化を使う。
規約：積表示は fiber 性を仮定しない明示的な比較データ。使われ方：dg の LT 切除。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- S の長方形の E 像を、c の分裂で実積に表示するための全図式データ。 -/
structure RelativeProductPullbackPresentation {S : SSet.{u + 1}}
    {ν : S ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierRectangle ν) (E : S ⟶ Sp.{u})
    {T X Y Z : OmegaSpectrum.{u}} (a : T ⟶ X) (b : T ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) where
  square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u}
  comparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.comparisonSquare ≫ E) square
  top_eq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ square =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.map f g)).edge
  right_eq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ square =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (BinaryGraph.diagonal Z)).edge
  left_eq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ square =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.lift a b)).edge

namespace RelativeProductPullbackPresentation
variable {S : SSet.{u + 1}} {ν : S ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}} {E : S ⟶ Sp.{u}}
  {d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierRectangle ν} (hE : IsRelativeLocalizingInvariant ν E)
  {T X Y Z : OmegaSpectrum.{u}} {a : T ⟶ X} {b : T ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  (v : RelativeProductPullbackPresentation d E a b f g)
  (hc : SpectrumHo.hom a ≫ SpectrumHo.hom f = SpectrumHo.hom b ≫ SpectrumHo.hom g)

/-- 比較同型も S 内にある場合は、その同じ E 像から積表示を作れる。 -/
def ofSourceIso (P : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso d.comparisonSquare P)
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (P ≫ E) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.map f g)).edge)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (P ≫ E) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (BinaryGraph.diagonal Z)).edge)
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (P ≫ E) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.lift a b)).edge) :
    RelativeProductPullbackPresentation d E a b f g :=
  ⟨P ≫ E, e.postcomp E, ht, hr, hl⟩

include hE in
lemma productSquare_isPullback : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare v.square :=
  ((_root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.comparisonSquare_isPullback d) hE).of_functorIso v.comparison

/-- 元の四辺 a,b,f,g を保つ相対 d8 の実 pullback。 -/
def normalizedSquare := BinaryProductCospanNormalized.square a b f g hc v.square
  (v.productSquare_isPullback hE) v.top_eq v.right_eq v.left_eq

lemma normalizedSquare_isPullback : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (v.normalizedSquare hE hc) :=
  BinaryProductCospanNormalized.square_isPullback _ _ _ _ _ _ _ _ _ _

lemma normalizedSquare_bottom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ v.normalizedSquare hE hc =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).edge :=
  BinaryProductCospanNormalized.square_bottom _ _ _ _ _ _ _ _ _ _

lemma normalizedSquare_left : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ v.normalizedSquare hE hc =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge b).edge :=
  BinaryProductCospanNormalized.square_left _ _ _ _ _ _ _ _ _ _

lemma normalizedSquare_right : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ v.normalizedSquare hE hc =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge :=
  BinaryProductCospanNormalized.square_right _ _ _ _ _ _ _ _ _ _

lemma normalizedSquare_top : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ v.normalizedSquare hE hc =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).edge :=
  BinaryProductCospanNormalized.square_top _ _ _ _ _ _ _ _ _ _

/-- 同じ実 cospan 上で、元の T を頂点に持つ極限錐。 -/
def normalizedCone := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (v.normalizedSquare hE hc)

lemma normalizedCone_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (v.normalizedCone hE hc) :=
  v.normalizedSquare_isPullback hE hc

lemma normalizedCone_vertex : (v.normalizedCone hE hc).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex T := by
  have hv := FiberModel.coneSquare_apex (v.normalizedCone hE hc)
  have hs : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (v.normalizedCone hE hc) = v.normalizedSquare hE hc := by
    simp only [normalizedCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare, Iso.inv_hom_id_assoc]
  rw [hs] at hv
  exact hv.symm.trans (NativeSquareRows.vertex00 _ _ (v.normalizedSquare_bottom hE hc))

end RelativeProductPullbackPresentation
end SerrePositivity.KST.LocalizingInvariants
