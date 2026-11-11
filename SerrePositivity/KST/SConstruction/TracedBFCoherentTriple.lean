module
public import SerrePositivity.KST.SConstruction.TracedBFCoherentComposition
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleTetrahedron
public import SerrePositivity.KST.SConstruction.CoherentTriangleMappingEdge

/-! # 三入力の元の三合成面を同時に保持する BF 四面体
概要：前二射・後二射・右結合の元の全合成面を三面に保持する実四面体を構成する。
方針：同じ六辺を持つ第一内ホーンを充填し、独立に指定した左結合の面と比較可能にする。
規約：生成される第四面と既存の第四面の一致・高次 coherence は未証明として区別する。
使われ方：元の BF 比較を保持した三入力の共有面の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
local instance tracedTripleSpectrumSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance tracedTripleSpectrumQuasicategory :
    Quasicategory (SimplicialNerve OmegaSpectrum.{u}) := sp_quasicategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 前二射・後二射・右結合の元の全合成面を三面に持つ実四面体。 -/
def monicKTracedCoherentTripleData :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compositionTripleTetrahedron (monicKTracedCoherentComposition F f g)
    (monicKTracedCoherentComposition F g h) (monicKTracedCoherentComposition F f (g ≫ h))

/-- 元の指定左結合面の全単体を保持して長辺の表示を移した同じデータ。 -/
def monicKTracedCoherentTriplePrescribedLeftData :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compositionTriangleLongEdgeData (monicKTracedCoherentComposition F (f ≫ g) h)
    (congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (monicKTracedSpectrumMap F k)).edge)
      (Category.assoc f g h))

/-- 左結合入力に対して既に指定した元の全合成面を、同じ長辺の表示へ移す。 -/
def monicKTracedCoherentTriplePrescribedLeft : SSet.Edge.CompStruct
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (monicKTracedSpectrumMap F (f ≫ g)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (monicKTracedSpectrumMap F h))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (monicKTracedSpectrumMap F (f ≫ g ≫ h))) :=
  (monicKTracedCoherentTriplePrescribedLeftData F f g h).val

/-- 表示の移送は元の指定左結合面の全二単体を変更しない。 -/
lemma monicKTracedCoherentTriplePrescribedLeft_simplex :
    (monicKTracedCoherentTriplePrescribedLeft F f g h).simplex =
      (monicKTracedCoherentComposition F (f ≫ g) h).simplex :=
  (monicKTracedCoherentTriplePrescribedLeftData F f g h).property

/-- 同じ四面体の前二射の面は、先に保存した元の合成面全体。 -/
lemma monicKTracedCoherentTriple_first_face :
    (SimplicialNerve OmegaSpectrum.{u}).δ 3
        (monicKTracedCoherentTripleData F f g h).simplex =
      (monicKTracedCoherentComposition F f g).simplex :=
  (monicKTracedCoherentTripleData F f g h).first_face

/-- 同じ四面体の後二射の面も、先に保存した元の合成面全体。 -/
lemma monicKTracedCoherentTriple_second_face :
    (SimplicialNerve OmegaSpectrum.{u}).δ 0
        (monicKTracedCoherentTripleData F f g h).simplex =
      (monicKTracedCoherentComposition F g h).simplex :=
  (monicKTracedCoherentTripleData F f g h).second_face

/-- 同じ四面体の右結合面も、先に保存した元の合成面全体。 -/
lemma monicKTracedCoherentTriple_right_face :
    (SimplicialNerve OmegaSpectrum.{u}).δ 2
        (monicKTracedCoherentTripleData F f g h).simplex =
      (monicKTracedCoherentComposition F f (g ≫ h)).simplex :=
  (monicKTracedCoherentTripleData F f g h).right_face

/-- 三つの元の面を保持する四面体から得た、同じ三辺を持つ左結合の実合成面。 -/
def monicKTracedCoherentTripleGeneratedLeft : SSet.Edge.CompStruct
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (monicKTracedSpectrumMap F (f ≫ g)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (monicKTracedSpectrumMap F h))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (monicKTracedSpectrumMap F (f ≫ g ≫ h))) :=
  (monicKTracedCoherentTripleData F f g h).left

/-- 得られた左結合面は同じ四面体の第一面そのもの。 -/
lemma monicKTracedCoherentTripleGeneratedLeft_face :
    (monicKTracedCoherentTripleGeneratedLeft F f g h).simplex =
      (SimplicialNerve OmegaSpectrum.{u}).δ 1
        (monicKTracedCoherentTripleData F f g h).simplex :=
  (monicKTracedCoherentTripleData F f g h).left_face

/-- 得られた左結合面の全単体を復号した、長辺から二辺の合成への実豊穣辺。 -/
def monicKTracedCoherentTripleGeneratedEdge :=
  coherentTriangleMappingEdge (monicKTracedSpectrumMap F (f ≫ g))
    (monicKTracedSpectrumMap F h) (monicKTracedSpectrumMap F (f ≫ g ≫ h))
    (monicKTracedCoherentTripleGeneratedLeft F f g h)

/-- 元の指定左結合面の全単体を復号した、同じ両端を持つ実豊穣辺。 -/
def monicKTracedCoherentTriplePrescribedEdge :=
  coherentTriangleMappingEdge (monicKTracedSpectrumMap F (f ≫ g))
    (monicKTracedSpectrumMap F h) (monicKTracedSpectrumMap F (f ≫ g ≫ h))
    (monicKTracedCoherentTriplePrescribedLeft F f g h)

end SerrePositivity.KST.SConstruction
