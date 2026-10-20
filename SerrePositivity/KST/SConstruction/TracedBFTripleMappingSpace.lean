module
public import SerrePositivity.KST.SConstruction.TracedBFTripleComparisonEdges

/-! # 三入力四面体の Hom 表示を元の実 BF 写像空間へ同定
概要：保存した二つの合成面から始終対象を回収し、元の BF 写像空間との表示等号を得る。
方針：四頂点の厳密な回収を Hom に適用し、二つの元の Path 三角形の共通対角辺も回収する。
規約：表示の等号を用い、写像空間の弱同値や π 群の同型に置き換えない。
使われ方：元の三入力の全二単体を同じ BF 写像空間へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet Spectra
open scoped Simplicial
local instance tracedTripleMappingSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の三入力四面体の始終 Hom は、元の同じ二対象の実 BF 写像空間と表示等号で一致。 -/
lemma monicKTracedCoherentTripleMappingSpace_eq :
    SimplicialCategory.sHom
      ((monicKTracedCoherentTripleData F f g h).simplex.obj (.mk (ULift.up 0)))
      ((monicKTracedCoherentTripleData F f g h).simplex.obj (.mk (ULift.up 3))) =
      OmegaSpectrum.mappingSpace (kOmegaSpectrum (F.obj w)) (kOmegaSpectrum (F.obj z)) := by
  have hv := coherentTetrahedron_vertices (monicKTracedCoherentTripleData F f g h).simplex
    (monicKTracedSpectrumMap F f) (monicKTracedSpectrumMap F g) (monicKTracedSpectrumMap F h)
    (monicKTracedSpectrumMap F (f ≫ g)) (monicKTracedSpectrumMap F (g ≫ h))
    (monicKTracedCoherentComposition F f g) (monicKTracedCoherentComposition F g h)
    (monicKTracedCoherentTriple_first_face F f g h)
    (monicKTracedCoherentTriple_second_face F f g h)
  exact congrArg₂ (fun A B : OmegaSpectrum.{u} => SimplicialCategory.sHom A B) hv.1 hv.2.2.2

/-- 元の二つの全 Path 三角形は、同じ四面体の同じ全対角辺を共有する。 -/
lemma monicKTracedCoherentTriplePathTriangles_diagonal :
    (SimplicialCategory.sHom
      ((monicKTracedCoherentTripleData F f g h).simplex.obj (.mk (ULift.up 0)))
      ((monicKTracedCoherentTripleData F f g h).simplex.obj (.mk (ULift.up 3)))).δ 1
        (monicKTracedCoherentTripleFirstPathTriangle F f g h).simplex =
      (SimplicialCategory.sHom
        ((monicKTracedCoherentTripleData F f g h).simplex.obj (.mk (ULift.up 0)))
        ((monicKTracedCoherentTripleData F f g h).simplex.obj (.mk (ULift.up 3)))).δ 1
          (monicKTracedCoherentTripleSecondPathTriangle F f g h).simplex :=
  coherentDoubleInsertMappedTriangles_diagonal (monicKTracedCoherentTriplePathMap F f g h)
    (show (ULift.up (0 : Fin 4) : ULift.{u} _) ≤ ULift.up 1 from by decide)
    (show (ULift.up (1 : Fin 4) : ULift.{u} _) ≤ ULift.up 3 from by decide)
    (show (ULift.up (0 : Fin 4) : ULift.{u} _) ≤ ULift.up 2 from by decide)
    (show (ULift.up (2 : Fin 4) : ULift.{u} _) ≤ ULift.up 3 from by decide)
    (coherentEndpointPath (show (ULift.up (0 : Fin 4) : ULift.{u} _) ≤ ULift.up 3 from by decide))

end SerrePositivity.KST.SConstruction
