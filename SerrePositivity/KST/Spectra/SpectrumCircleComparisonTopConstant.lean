module

public import SerrePositivity.KST.Spectra.SpectrumCircleComparisonCellObjects
public import SerrePositivity.KST.Spectra.RawSpectrumPointedBasepointComposition

/-!
概要：元の錐の比較の Hom 正方形の上辺は、元の一点を通るため定値。
方針：一点への・一点からの全 Hom の終対象性と、元の基点の合成式を使う。
規約：三角形の trace を消去せず実際の合成から示す。使われ方：比較正方形の経路の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleComparisonTopSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の一点 BF スペクトルを経由する全パラメータの豊穣合成は、元の零 Hom に定値。 -/
lemma composition_through_point_constant (X P Y : OmegaSpectrum.{u}) (hP : P = _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint)
    {A : SSet.{u}} (f : A ⟶ SimplicialCategory.sHom X P)
    (g : A ⟶ SimplicialCategory.sHom P Y) :
    lift f g ≫ eComp SSet X P Y =
      SSet.const (RawSpectrumMapping.pointedSpace X Y.toKanSequence).basepoint := by
  subst P
  have hf := (mappingPoint_isTerminal X).hom_ext f
    (toUnit A ≫ (RawSpectrumMapping.pointedSpace X _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint.toKanSequence).hom)
  have hg := (pointMapping_isTerminal Y).hom_ext g
    (toUnit A ≫ (RawSpectrumMapping.pointedSpace _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint Y.toKanSequence).hom)
  rw [hf, hg, ← comp_lift, Category.assoc]
  have hc := RawSpectrumMapping.basepoint_composition X _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint Y.toKanSequence
  change lift (RawSpectrumMapping.pointedSpace X _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint.toKanSequence).hom
    (RawSpectrumMapping.pointedSpace _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint Y.toKanSequence).hom ≫
      eComp SSet X _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint Y = (RawSpectrumMapping.pointedSpace X Y.toKanSequence).hom at hc
  rw [hc]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const _ _

/-- 元の比較三単体の Hom 正方形の上辺は、元の一点を経由する同じ合成なので定値。 -/
lemma circleCompanionComparisonTrace_includeSecond_constant (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) :
    ∃ v, lift (𝟙 (Δ[1] : SSet.{u}))
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
        CoherentPathCoordinates.tetrahedronTrace (circleCompanionComparisonTetrahedron z k) =
      SSet.const v := by
  rw [CoherentPathCoordinates.tetrahedronTrace_includeSecond]
  exact ⟨_, composition_through_point_constant _ _ _
    (circleCompanionComparisonTetrahedron_obj_two z k) _ _⟩

/-- 元の全 Hom に表示した比較正方形の上辺も、同じ元の定値経路。 -/
lemma circleCompanionComparisonRawHomSquare_includeSecond_constant (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) :
    ∃ v, lift (𝟙 (Δ[1] : SSet.{u}))
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
      circleCompanionComparisonRawHomSquare z k = SSet.const v := by
  obtain ⟨v, hv⟩ := circleCompanionComparisonTrace_includeSecond_constant z k
  let m : SimplicialCategory.sHom
      ((circleCompanionComparisonTetrahedron z k).obj ⟨ULift.up 0⟩)
      ((circleCompanionComparisonTetrahedron z k).obj ⟨ULift.up 3⟩) ⟶
      (circleEvaluationPointedHom z).right :=
    eqToHom (congrArg (fun s : Sp.{u} _⦋2⦌ ↦
      SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))
      (circleCompanionComparisonTetrahedron_two z k)) ≫ eqToHom (circleComparisonCentralHom_eq z)
  have h : lift (𝟙 (Δ[1] : SSet.{u}))
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
      CoherentPathCoordinates.tetrahedronTrace (circleCompanionComparisonTetrahedron z k) ≫ m =
      SSet.const (m.app (Opposite.op ⦋0⦌) v) := by
    rw [← Category.assoc, hv, SSet.const_comp]
  refine ⟨m.app (Opposite.op ⦋0⦌) v, ?_⟩
  simpa only [circleCompanionComparisonRawHomSquare, circleCompanionComparisonHomSquare,
    CoherentPathCoordinates.tetrahedronTraceAgainst, m, Category.assoc] using h

end SerrePositivity.KST.Spectra.OmegaSpectrum
