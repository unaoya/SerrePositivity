module

public import SerrePositivity.KST.Spectra.SpectrumZeroEvaluationTriangle

/-!
概要：元の Sp 上での零評価の、定値零図式を中間に持つ coherent な三角形の族。
方針：共通解像の源射影の逆を合成し、各頂点と関手単体集合の零対象を厳密に同定する。
規約：安定性を仮定しない。使われ方：円の Hom-loop と零角を持つ四角形の比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance nativeZeroTriangleSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の Sp 上で、零対象経由の因子分解を持つ実際の三角形の族。 -/
def nativeZeroEvaluationTriangleFamily (A : PointedSimplicialSet.{u}) :
    Sp.{u} ⊗ (Δ[2] : SSet.{u + 1}) ⟶ Sp.{u} :=
  ((CotensorCompatible.sourceInfinityEquivalence A).inv ⊗ₘ 𝟙 _) ≫
    CotensorCompatible.zeroEvaluationTriangleFamily A

/-- 源射影の逆による移送は、三角形の全頂点の評価と厳密に可換。 -/
lemma nativeZeroEvaluationTriangleFamily_vertex (A : PointedSimplicialSet.{u}) (i : Fin 3) :
    lift (𝟙 Sp.{u}) (SSet.const (stdSimplex.obj₀Equiv.symm i)) ≫
        nativeZeroEvaluationTriangleFamily A =
      (CotensorCompatible.sourceInfinityEquivalence A).inv ≫
        lift (𝟙 (SimplicialNerve (CotensorCompatible.Object A)))
          (SSet.const (stdSimplex.obj₀Equiv.symm i)) ≫
            CotensorCompatible.zeroEvaluationTriangleFamily A := by
  have h : lift (𝟙 Sp.{u}) (SSet.const (stdSimplex.obj₀Equiv.symm i)) ≫
      ((CotensorCompatible.sourceInfinityEquivalence A).inv ⊗ₘ 𝟙 (Δ[2] : SSet.{u + 1})) =
      (CotensorCompatible.sourceInfinityEquivalence A).inv ≫
        lift (𝟙 (SimplicialNerve (CotensorCompatible.Object A)))
          (SSet.const (stdSimplex.obj₀Equiv.symm i)) := rfl
  rw [nativeZeroEvaluationTriangleFamily, ← Category.assoc, h, Category.assoc]

/-- 三角形の最初の頂点図式は元の native cotensor 関手。 -/
lemma nativeZeroEvaluationTriangleFamily_zero (A : PointedSimplicialSet.{u}) :
    lift (𝟙 Sp.{u}) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 3))) ≫
      nativeZeroEvaluationTriangleFamily A = nativeCotensor A := by
  rw [nativeZeroEvaluationTriangleFamily_vertex,
    CotensorCompatible.zeroEvaluationTriangleFamily_zero]
  rfl

/-- 三角形の中間の頂点図式は元の定値零図式そのもの。 -/
lemma nativeZeroEvaluationTriangleFamily_one (A : PointedSimplicialSet.{u}) :
    lift (𝟙 Sp.{u}) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 3))) ≫
      nativeZeroEvaluationTriangleFamily A = constantZeroDiagram Sp.{u} := by
  rw [nativeZeroEvaluationTriangleFamily_vertex,
    CotensorCompatible.zeroEvaluationTriangleFamily_one,
    constantZeroDiagram, SSet.comp_const]
  rfl

/-- 三角形の中間の頂点は、関手単体集合でも実際の零対象。 -/
lemma nativeZeroEvaluationTriangleFamily_middle_isZero (A : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      (lift (𝟙 Sp.{u}) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 3))) ≫
        nativeZeroEvaluationTriangleFamily A)) := by
  rw [nativeZeroEvaluationTriangleFamily_one]
  exact (functorZeroVertex Sp.{u}).isZero

/-- 三角形の最後の頂点図式は恒等関手と実際に関手同型。 -/
def nativeZeroEvaluationTriangleFamily_targetIso (A : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (lift (𝟙 Sp.{u}) (SSet.const (stdSimplex.obj₀Equiv.symm (2 : Fin 3))) ≫
        nativeZeroEvaluationTriangleFamily A) (𝟙 Sp.{u}) := by
  rw [nativeZeroEvaluationTriangleFamily_vertex,
    CotensorCompatible.zeroEvaluationTriangleFamily_two]
  exact (CotensorCompatible.sourceInfinityEquivalence A).invHomIso

end SerrePositivity.KST.Spectra.OmegaSpectrum
