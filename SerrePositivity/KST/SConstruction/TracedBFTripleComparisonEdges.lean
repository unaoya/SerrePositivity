module
public import SerrePositivity.KST.SConstruction.TracedBFTriplePathDiamond
public import SerrePositivity.KST.SConstruction.CoherentTetrahedronWhiskeredEdges

/-! # 三入力 BF 二経路の四辺と元の保存面の比較辺
概要：同じ四面体から得る二つの実二単体の四辺を、保存面の比較辺と実 BF 合成へ照合する。
方針：一般の全辺の等式と、保存した全二単体の面等式を同じ四面体に適用する。
規約：全一単体を依存等号で回収し、元の面とその二次元データを選び直さない。
使われ方：生成された第四面と独立に指定した左結合面の比較への入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
local instance tracedTripleComparisonSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 第一経路の下辺は、元の右結合の保存面から復号した全比較辺。 -/
lemma monicKTracedCoherentTripleFirstLower_heq :
    HEq ((SimplicialCategory.sHom
      ((monicKTracedCoherentTripleData F f g h).simplex.obj (.mk (ULift.up 0)))
      ((monicKTracedCoherentTripleData F f g h).simplex.obj (.mk (ULift.up 3)))).δ 2
        (monicKTracedCoherentTripleFirstPathTriangle F f g h).simplex)
      (coherentTriangleMappingEdge (monicKTracedSpectrumMap F f)
        (monicKTracedSpectrumMap F (g ≫ h)) (monicKTracedSpectrumMap F (f ≫ g ≫ h))
        (monicKTracedCoherentComposition F f (g ≫ h))).edge := by
  have hl := coherentSimplexFirstInsertion_lower
    (monicKTracedCoherentTripleData F f g h).simplex 0 1 2 3
    (by decide) (by decide) (by decide)
  exact (heq_of_eq hl).trans (coherentTetrahedronFaceComparison_heq _ 2
    (monicKTracedSpectrumMap F f) (monicKTracedSpectrumMap F (g ≫ h))
    (monicKTracedSpectrumMap F (f ≫ g ≫ h)) (monicKTracedCoherentComposition F f (g ≫ h))
    (monicKTracedCoherentTriple_right_face F f g h))

/-- 第二経路の下辺は、同じ四面体の生成された左結合面の全比較辺。 -/
lemma monicKTracedCoherentTripleSecondLower_heq :
    HEq ((SimplicialCategory.sHom
      ((monicKTracedCoherentTripleData F f g h).simplex.obj (.mk (ULift.up 0)))
      ((monicKTracedCoherentTripleData F f g h).simplex.obj (.mk (ULift.up 3)))).δ 2
        (monicKTracedCoherentTripleSecondPathTriangle F f g h).simplex)
      (monicKTracedCoherentTripleGeneratedEdge F f g h).edge := by
  have hl := coherentSimplexSecondInsertion_lower
    (monicKTracedCoherentTripleData F f g h).simplex 0 1 2 3
    (by decide) (by decide) (by decide)
  exact (heq_of_eq hl).trans (coherentTetrahedronFaceComparison_heq _ 1
    (monicKTracedSpectrumMap F (f ≫ g)) (monicKTracedSpectrumMap F h)
    (monicKTracedSpectrumMap F (f ≫ g ≫ h)) (monicKTracedCoherentTripleGeneratedLeft F f g h)
    (monicKTracedCoherentTripleGeneratedLeft_face F f g h).symm)

/-- 第一経路の上辺は、元の第一射と保存した後二射の比較辺の同じ BF 合成。 -/
lemma monicKTracedCoherentTripleFirstUpper_heq :
    HEq ((SimplicialCategory.sHom
      ((monicKTracedCoherentTripleData F f g h).simplex.obj (.mk (ULift.up 0)))
      ((monicKTracedCoherentTripleData F f g h).simplex.obj (.mk (ULift.up 3)))).δ 0
        (monicKTracedCoherentTripleFirstPathTriangle F f g h).simplex)
      ((OmegaSpectrum.mappingComposition (kOmegaSpectrum (F.obj w))
        (kOmegaSpectrum (F.obj x)) (kOmegaSpectrum (F.obj z))).app (Opposite.op ⦋1⦌)
        ((SSet.Edge.id (SimplicialCategory.homEquiv' _ _
            (monicKTracedSpectrumMap F f))).edge,
          (coherentTriangleMappingEdge (monicKTracedSpectrumMap F g)
            (monicKTracedSpectrumMap F h) (monicKTracedSpectrumMap F (g ≫ h))
            (monicKTracedCoherentComposition F g h)).edge)) :=
  coherentTetrahedronFirstUpper_heq (monicKTracedCoherentTripleData F f g h).simplex
    (monicKTracedSpectrumMap F f) (monicKTracedSpectrumMap F g) (monicKTracedSpectrumMap F h)
    (monicKTracedSpectrumMap F (f ≫ g)) (monicKTracedSpectrumMap F (g ≫ h))
    (monicKTracedCoherentComposition F f g) (monicKTracedCoherentComposition F g h)
    (monicKTracedCoherentTriple_first_face F f g h)
    (monicKTracedCoherentTriple_second_face F f g h)

/-- 第二経路の上辺は、保存した前二射の比較辺と元の最終射の同じ BF 合成。 -/
lemma monicKTracedCoherentTripleSecondUpper_heq :
    HEq ((SimplicialCategory.sHom
      ((monicKTracedCoherentTripleData F f g h).simplex.obj (.mk (ULift.up 0)))
      ((monicKTracedCoherentTripleData F f g h).simplex.obj (.mk (ULift.up 3)))).δ 0
        (monicKTracedCoherentTripleSecondPathTriangle F f g h).simplex)
      ((OmegaSpectrum.mappingComposition (kOmegaSpectrum (F.obj w))
        (kOmegaSpectrum (F.obj y)) (kOmegaSpectrum (F.obj z))).app (Opposite.op ⦋1⦌)
        ((coherentTriangleMappingEdge (monicKTracedSpectrumMap F f)
            (monicKTracedSpectrumMap F g) (monicKTracedSpectrumMap F (f ≫ g))
            (monicKTracedCoherentComposition F f g)).edge,
          (SSet.Edge.id (SimplicialCategory.homEquiv' _ _
            (monicKTracedSpectrumMap F h))).edge)) :=
  coherentTetrahedronSecondUpper_heq (monicKTracedCoherentTripleData F f g h).simplex
    (monicKTracedSpectrumMap F f) (monicKTracedSpectrumMap F g) (monicKTracedSpectrumMap F h)
    (monicKTracedSpectrumMap F (f ≫ g)) (monicKTracedSpectrumMap F (g ≫ h))
    (monicKTracedCoherentComposition F f g) (monicKTracedCoherentComposition F g h)
    (monicKTracedCoherentTriple_first_face F f g h)
    (monicKTracedCoherentTriple_second_face F f g h)

end SerrePositivity.KST.SConstruction
