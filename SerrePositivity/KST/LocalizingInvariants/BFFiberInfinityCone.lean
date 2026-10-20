module

public import SerrePositivity.KST.LocalizingInvariants.RawFiberInfinityCone
public import SerrePositivity.KST.LocalizingInvariants.LimitVertexTransport
public import SerrePositivity.KST.Spectra.SpectrumCospanReplacement
public import SerrePositivity.KST.LocalizingInvariants.StrictConeTransport

/-!
概要：長完全列の元の BF fiber を頂点とする Sp の極限錐。
方針：段ごとの比較同値を slice 内で持ち上げ、任意射では fibration 置換の図式同型で戻す。
規約：fiber 対象を取り替えない。包含との比較の証拠は置換後の図式上で保持する。
使われ方：K-5 の任意の fiber 列への長完全列の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberModel

local instance bfFiberSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance bfFiberHomKan (E B : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom E B) := OmegaSpectrum.mappingSpace_kanComplex E B

variable {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y) [hp : ∀ n, Fibration (p.app n).right]

/-- 元の BF fiber への頂点変更と、比較射上の slice の辺を同時に選ぶ。 -/
lemma exists_replacedCone :
    ∃ c : JoinCone (strictCoherentDiagram (spectrumPullbackDiagram p (fromPoint Y))),
      IsLimitCone c ∧ c.vertex = coherentNerveVertex (fiber p hp) ∧
      ∃ a : SSet.Truncated.Edge
          (X := (truncation 2).obj (sliceOver
            (strictCoherentDiagram (spectrumPullbackDiagram p (fromPoint Y))))) c (infinityCone p),
        (a.map ((truncation 2).map (sliceOverProjection _))).edge =
          (coherentNerveEdge (comparison p hp)).edge := by
  let e := (coherentNerveEdge (comparison p hp)).ofEq rfl (infinityCone_vertex p).symm
  have he : IsInvertibleEdge e.toTruncated :=
    (isInvertibleEdge_congr (e := (coherentNerveEdge (comparison p hp)).toTruncated)
      (f := e.toTruncated) rfl).mp (comparison_isInvertible p hp)
  exact ConeVertexTransport.exists_limitCone (infinityCone p) (infinityCone_isLimit p)
    e he

/-- 長完全列の元の置換済み BF fiber を頂点に持つ錐。 -/
def replacedCone : JoinCone (strictCoherentDiagram (spectrumPullbackDiagram p (fromPoint Y))) :=
  (exists_replacedCone p).choose

lemma replacedCone_isLimit : IsLimitCone (replacedCone p) :=
  (exists_replacedCone p).choose_spec.1

lemma replacedCone_vertex : (replacedCone p).vertex = coherentNerveVertex (fiber p hp) :=
  (exists_replacedCone p).choose_spec.2.1

/-- 置換後の錐と段ごとの fiber の錐の間の、同じ図式上の比較。 -/
def replacedConeComparison : SSet.Truncated.Edge
    (X := (truncation 2).obj (sliceOver
      (strictCoherentDiagram (spectrumPullbackDiagram p (fromPoint Y)))))
    (replacedCone p) (infinityCone p) :=
  (exists_replacedCone p).choose_spec.2.2.choose

lemma replacedConeComparison_projection :
    ((replacedConeComparison p).map ((truncation 2).map (sliceOverProjection _))).edge =
      (coherentNerveEdge (comparison p hp)).edge :=
  (exists_replacedCone p).choose_spec.2.2.choose_spec

/-- 置換単位の元の円柱を保持した、元の cospan への錐の輸送。 -/
def homotopyFiberTransport {E B : OmegaSpectrum.{u}} (f : E ⟶ B) :
    F2.SpecifiedLimitConeTransport
      (p := strictCoherentDiagram (spectrumPullbackDiagram f (fromPoint B)))
      (F2.strictCoherentNatTransMap (CospanReplacement.unit f (fromPoint B)))
      (replacedCone (fibrationReplacementProjection f)) :=
  StrictConeTransport.transport (CospanReplacement.unit f (fromPoint B))
    (CospanReplacement.unit_isInvertible f (fromPoint B))
    (replacedCone (fibrationReplacementProjection f))
    (replacedCone_isLimit (fibrationReplacementProjection f))

/-- 任意射の元の homotopyFiber を頂点とする、元の cospan 上の極限錐の存在。 -/
lemma homotopyFiber_exists_limitCone {E B : OmegaSpectrum.{u}} (f : E ⟶ B) :
    ∃ c : JoinCone (strictCoherentDiagram (spectrumPullbackDiagram f (fromPoint B))),
      IsLimitCone c ∧ c.vertex = coherentNerveVertex (homotopyFiber f) := by
  let t := homotopyFiberTransport f
  exact ⟨t.cone, t.isLimit,
    t.vertex_eq.trans (replacedCone_vertex (fibrationReplacementProjection f))⟩

def homotopyFiberCone {E B : OmegaSpectrum.{u}} (f : E ⟶ B) :
    JoinCone (strictCoherentDiagram (spectrumPullbackDiagram f (fromPoint B))) :=
  (homotopyFiberTransport f).cone

lemma homotopyFiberCone_isLimit {E B : OmegaSpectrum.{u}} (f : E ⟶ B) :
    IsLimitCone (homotopyFiberCone f) := (homotopyFiberTransport f).isLimit

lemma homotopyFiberCone_vertex {E B : OmegaSpectrum.{u}} (f : E ⟶ B) :
    (homotopyFiberCone f).vertex = coherentNerveVertex (homotopyFiber f) :=
  (homotopyFiberTransport f).vertex_eq.trans
    (replacedCone_vertex (fibrationReplacementProjection f))

end SerrePositivity.KST.LocalizingInvariants.FiberModel
