module

public import SerrePositivity.KST.Spectra.D3NativeLoopSource
public import SerrePositivity.KST.Spectra.D3RawHomVertices
public import SerrePositivity.KST.Spectra.KanCompositeCancellation

/-!
概要：実 loop 頂点へ写る BF 始点に、元の補助単位の厳密な延長を構成する。
方針：相対左因子の全 Raw Hom 前合成の自明 Kan fibration から切断を取り、実列射を回収する。
規約：選択した切断の標的・源の自然性は主張しない。全 Hom の同時整合は後続工程。
使われ方：d3b② の実二因子 X→L_X→T_X と元の単位の厳密回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 相対左因子の全 Hom の射影に対する実切断。自然な切断とは主張しない。 -/
def loopSourcePreSection (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) :
    RawSpectrumMapping.space X Y ⟶ RawSpectrumMapping.space (loopSource X) Y := by
  let := loopSourcePre_trivialKanFibration X Y
  exact Classical.choose
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (RawSpectrumMapping.pre (loopSourceInclusion X) Y))

/-- 同じ切断と元の前合成は全単体で厳密に恒等射を回収する。 -/
@[reassoc]
lemma loopSourcePreSection_fac (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) :
    loopSourcePreSection X Y ≫ RawSpectrumMapping.pre (loopSourceInclusion X) Y = 𝟙 _ := by
  let := loopSourcePre_trivialKanFibration X Y
  exact Classical.choose_spec
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (RawSpectrumMapping.pre (loopSourceInclusion X) Y))

/-- 元の補助単位の同じ零単体を、実 BF 始点へ延長した全 Hom の点。 -/
def loopSourceUnitFamily (X : OmegaSpectrum.{u}) :
    𝟙_ SSet.{u} ⟶ RawSpectrumMapping.space (loopSource X) (target X) :=
  RawSpectrumMapping.d3VertexMap X (target X) (KanSequence.adjointLoopTailUnit X.toKanSequence) ≫
    loopSourcePreSection X (target X)

/-- 同じ延長族は左因子に制限すると元の補助単位自体を厳密回収する。 -/
lemma loopSourceUnitFamily_fac (X : OmegaSpectrum.{u}) :
    loopSourceUnitFamily X ≫ RawSpectrumMapping.pre (loopSourceInclusion X) (target X) =
      RawSpectrumMapping.d3VertexMap X (target X)
        (KanSequence.adjointLoopTailUnit X.toKanSequence) := by
  rw [loopSourceUnitFamily, Category.assoc, loopSourcePreSection_fac, Category.comp_id]

/-- 実 BF 始点から元の補助標的への実列射。存在を新仮定に残さない。 -/
def loopSourceProjection (X : OmegaSpectrum.{u}) :
    KanSequence.Hom (loopSource X).toKanSequence (target X) :=
  RawSpectrumMapping.d3HomOfVertex (loopSource X) (target X)
    ((RawSpectrumMapping.space (loopSource X) (target X)).unitHomEquiv (loopSourceUnitFamily X))

/-- 実二因子 X→L_X→T_X の合成は、元の補助単位そのもの。 -/
lemma loopSourceProjection_fac (X : OmegaSpectrum.{u}) (n : ℕ) :
    (loopSourceInclusion X).app n ≫ (loopSourceProjection X).app n =
      (KanSequence.adjointLoopTailUnit X.toKanSequence).app n := by
  have h := congrArg ((RawSpectrumMapping.space X (target X)).unitHomEquiv)
    (loopSourceUnitFamily_fac X)
  rw [unitHomEquiv_comp] at h
  have hp := RawSpectrumMapping.d3HomOfVertex_pre (loopSourceInclusion X) (target X)
    ((RawSpectrumMapping.space (loopSource X) (target X)).unitHomEquiv
      (loopSourceUnitFamily X)) n
  rw [h, RawSpectrumMapping.d3HomOfVertex_app,
    RawSpectrumMapping.d3VertexMap_evaluation] at hp
  simpa only [OmegaSpectrum.toKanSequence, target, Equiv.symm_apply_apply,
    loopSourceProjection] using hp.symm

/-- 構成した右脚自身も全段の全基点 π 同型。元の単位と左因子から消去する。 -/
lemma loopSourceProjection_levelwise (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((loopSourceProjection X).app n).right := by
  apply (_root_.SerrePositivity.KST.Spectra.KanPiIsomorphism.cancel_left_atVertex (loopSourceInclusion_levelwise X n))
    (x := PointedSimplicialSet.basepoint (X.level n).space)
  rw [← Under.comp_right, loopSourceProjection_fac]
  exact KanSequence.adjointLoopTailUnit_levelwise X.toKanSequence_omega n

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
