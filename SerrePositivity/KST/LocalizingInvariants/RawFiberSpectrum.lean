module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyFiber
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.SmashMonomorphisms
public import SerrePositivity.KST.Spectra.SpectrumIntegerHomotopyDetection

/-!
概要：段ごとの実 fiber を置換せずに束ねた BF スペクトル。
方針：fiber 包含の単射性と元の構造射の単射性から fiber の構造射の単射性を導く。
規約：長完全列で使う元の置換済み fiber とその包含を変更しない。
使われ方：K-5 の実 BF fiber と Sp の極限錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberModel

/-- fiber 包含の基礎射は単射。 -/
lemma inclusion_mono {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) :
    Mono (pointedFiberι p).right := ⟨by
  intro Z a b h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p.right _ h⟩

/-- 元の単射な構造射から実 fiber の構造射の単射性を得る。 -/
lemma sigma_mono {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)
    (hp : ∀ n, Fibration (p.app n).right) (n : ℕ) :
    Mono ((sequenceHom p).fiberSigma n).right := by
  let : Mono (pointedFiberι (p.app n)).right := inclusion_mono _
  have hc := congrArg Under.Hom.right (((sequenceHom p).fiberInclusion hp).comm n)
  change (PointedSimplicialSet.circle.{u} ◁ pointedFiberι (p.app n)).right ≫
      (X.sigma n).right = ((sequenceHom p).fiberSigma n).right ≫
      (pointedFiberι (p.app (n + 1))).right at hc
  have hm : Mono ((PointedSimplicialSet.circle.{u} ◁ pointedFiberι (p.app n)).right ≫
      (X.sigma n).right) := by infer_instance
  have h : Mono (((sequenceHom p).fiberSigma n).right ≫
      (pointedFiberι (p.app (n + 1))).right) := hc ▸ hm
  exact mono_of_mono ((sequenceHom p).fiberSigma n).right
    (pointedFiberι (p.app (n + 1))).right

/-- 置換前の各段の実 fiber そのものを持つ BF 対象。 -/
def obj {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)
    (hp : ∀ n, Fibration (p.app n).right) : OmegaSpectrum.{u} :=
  ((sequenceHom p).fiber hp).toOmegaSpectrum (sigma_mono p hp)
    ((sequenceHom p).fiber_omegaCondition hp X.toKanSequence_omega Y.toKanSequence_omega)

/-- 置換前の fiber から元の全空間への包含。 -/
def inclusion {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)
    (hp : ∀ n, Fibration (p.app n).right) : obj p hp ⟶ X where
  app n := pointedFiberι (p.app n)
  comm := ((sequenceHom p).fiberInclusion hp).comm

/-- 長完全列の fiber から置換前の fiber への元の比較射。 -/
def comparison {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)
    (hp : ∀ n, Fibration (p.app n).right) : fiber p hp ⟶ obj p hp where
  app := (KanSequence.replacementProjection ((sequenceHom p).fiber hp)).app
  comm := (KanSequence.replacementProjection ((sequenceHom p).fiber hp)).comm

lemma comparison_levelwise {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)
    (hp : ∀ n, Fibration (p.app n).right) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((comparison p hp).app n).right :=
  fiberLevelProjection_piIsomorphism p hp n

/-- 比較射の後の包含は、長完全列で使う元の包含そのもの。 -/
lemma comparison_inclusion {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)
    (hp : ∀ n, Fibration (p.app n).right) :
    comparison p hp ≫ inclusion p hp = fiberInclusion p hp :=
  OmegaSpectrum.Hom.ext (fun _ ↦ rfl)

local instance rawFiberSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 比較は元の Sp の同じ辺における同値。 -/
lemma comparison_isInvertible {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)
    (hp : ∀ n, Fibration (p.app n).right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (comparison p hp)) :=
  isInvertible_of_piIsomorphism _ (piIsomorphism_of_levelwise _ (comparison_levelwise p hp))

end SerrePositivity.KST.LocalizingInvariants.FiberModel
