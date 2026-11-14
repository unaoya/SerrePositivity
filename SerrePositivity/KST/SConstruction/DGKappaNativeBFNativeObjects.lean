module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFArrowComparison
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFArrowStages

/-!
概要：元未完備 native 四角形の四対象と四射を同じ有限入力に保持する。
方針：元の全四角形の頂点等号から頂点像条件を回収する。
規約：元の零角・包含・商射を選び直さない。使われ方：新 BF 四辺の同時回収。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open NonConnective Spectra LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ native 零角は元の指定零安定圏の頂点。
方針：同じ実提示の左辺の終点を使う。
規約：零対象を選び直さない。使われ方：四対象の有限入力化。 -/
lemma dgKappaNativeBF_zeroVertex :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgKappaNativeVerdierDiagram.{u, v} R D I).square 0 1 =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{max (u + 1) v} := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target (dgKappaNativeVerdierDiagram.{u, v} R D I).square
  let ev := fun k : (Δ[1] : SSet.{max (u + 1) v + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v} =>
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v}).map (SimplexCategory.δ (0 : Fin 2)).op
      (SSet.yonedaEquiv k)
  have he := congrArg ev
    (VerdierSequence.presentation_left (dgKappaNativeVerdierSequence.{u, v} R D I))
  exact h.symm.trans (he.trans (by
    change _ = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory
    dsimp only [ev]
    rw [Equiv.apply_symm_apply]
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory
      (dgKappaNativeVerdierSequence.{u, v} R D I).left)).tgt_eq))

/-- 概要：元四角形の指定頂点を同じ充満有限入力へ保持する。
方針：元の頂点等号を復号して同じ頂点像の証人にする。
規約：通常対象は C のまま。使われ方：元の四辺の型付け。 -/
def dgKappaNativeBFFiniteObjectOfVertexEq (a b : Fin 2)
    (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{max (u + 1) v})
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgKappaNativeVerdierDiagram.{u, v} R D I).square a b = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex C) :
    DGKappaNativeBFFiniteInput.{u, v} R D I :=
  ⟨C, ⟨(stdSimplex.obj₀Equiv.symm a, stdSimplex.obj₀Equiv.symm b),
    congrArg (fun x => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{max (u + 1) v}) x) h⟩⟩

/-- 概要：元の始域・中間・零角・終域を同じ有限入力で保持する。
方針：元提示の三頂点等号と指定零角の等号を使う。
規約：番号は始域・中間・零・終域。使われ方：新四辺の端点。 -/
def dgKappaNativeBFFiniteNativeObject : Fin 4 → DGKappaNativeBFFiniteInput.{u, v} R D I :=
  ![dgKappaNativeBFFiniteObjectOfVertexEq.{u, v} R D I 0 0
      (dgKappaNativeVerdierDiagram.{u, v} R D I).left
      (dgKappaNativeVerdierDiagram.{u, v} R D I).left_eq,
    dgKappaNativeBFFiniteObjectOfVertexEq.{u, v} R D I 1 0
      (dgKappaNativeVerdierDiagram.{u, v} R D I).middle
      (dgKappaNativeVerdierDiagram.{u, v} R D I).middle_eq,
    dgKappaNativeBFFiniteObjectOfVertexEq.{u, v} R D I 0 1 _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory
      (dgKappaNativeBF_zeroVertex.{u, v} R D I),
    dgKappaNativeBFFiniteObjectOfVertexEq.{u, v} R D I 1 1
      (dgKappaNativeVerdierDiagram.{u, v} R D I).right
      (dgKappaNativeVerdierDiagram.{u, v} R D I).right_eq]

/-- 概要：元の包含・商・左右の零射を同じ有限入力の四射に保持する。
方針：同じ充満部分圏の通常 Hom を使う。
規約：順序は底・右・左・上。使われ方：実 Φ の新しい四 BF 辺。 -/
def dgKappaNativeBFFiniteNativeArrow :
    Fin 4 → Arrow (DGKappaNativeBFFiniteInput.{u, v} R D I) :=
  ![Arrow.mk (show dgKappaNativeBFFiniteNativeObject.{u, v} R D I 0 ⟶
      dgKappaNativeBFFiniteNativeObject.{u, v} R D I 1 from
        ObjectProperty.homMk (dgKappaNativeVerdierDiagram.{u, v} R D I).inclusion),
    Arrow.mk (show dgKappaNativeBFFiniteNativeObject.{u, v} R D I 1 ⟶
      dgKappaNativeBFFiniteNativeObject.{u, v} R D I 3 from
        ObjectProperty.homMk (dgKappaNativeVerdierDiagram.{u, v} R D I).projection),
    Arrow.mk (show dgKappaNativeBFFiniteNativeObject.{u, v} R D I 0 ⟶
      dgKappaNativeBFFiniteNativeObject.{u, v} R D I 2 from
        ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (dgKappaNativeVerdierDiagram.{u, v} R D I).left)),
    Arrow.mk (show dgKappaNativeBFFiniteNativeObject.{u, v} R D I 2 ⟶
      dgKappaNativeBFFiniteNativeObject.{u, v} R D I 3 from
        ObjectProperty.homMk (fromZeroCategory (dgKappaNativeVerdierDiagram.{u, v} R D I).right))]

local instance nativeCoherentBFArrowTarget_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

/-- 概要：同じ元四射の全 Hom から同時構成した四 BF 射。
方針：同じ有限入力の BF 豊穣関手の通常射を回収する。
規約：旧公開射を変更しない。使われ方：Φ の四辺と旧 K の整数群作用。 -/
def dgKappaNativeCoherentBFArrow (e : Fin 4) : Arrow OmegaSpectrum.{max (u + 1) v} :=
  Arrow.mk (dgKappaNativeBFFiniteArrow.{u, v} R D I
    (dgKappaNativeBFFiniteNativeArrow.{u, v} R D I e).hom)

end SerrePositivity.KST.SConstruction
