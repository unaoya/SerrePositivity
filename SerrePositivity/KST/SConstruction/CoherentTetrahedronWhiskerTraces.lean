module
public import SerrePositivity.KST.SConstruction.CoherentTriangleTraceRecovery
public import SerrePositivity.KST.Spectra.CoherentSimplexCompositionFaces
public import SerrePositivity.KST.Spectra.CoherentTriangleDegenerateTrace

/-! # 元の三単体の合成面の区間は元の辺による前後合成
概要：Hom 正方形の二つの合成面を、元の三角形の区間と最初・最後の射の前後合成に戻す。
方針：端点だけの Path の定数性と通常の豊穣射の作用を使う。
規約：元の単体・三角形・全時刻の区間を保存する。
使われ方：K 合成 prism の残る四辺を既存復号辺へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open Spectra.CoherentPathCoordinates SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の三単体の最初の Path は、同じ二端点 Path。 -/
lemma tetrahedronInitialPath_endpoint : tetrahedronInitialPath.{u} =
    coherentEndpointPath (show (ULift.up 0 : ULift.{u} (Fin 4)) ≤ ULift.up 1 from by decide) := by
  apply SimplicialThickening.Path.ext
  ext x
  obtain ⟨x⟩ := x
  fin_cases x <;> simp [tetrahedronInitialPath, coherentEndpointPath]

/-- 元の三単体の最後の Path も、同じ二端点 Path。 -/
lemma tetrahedronFinalPath_endpoint : tetrahedronFinalPath.{u} =
    coherentEndpointPath (show (ULift.up 2 : ULift.{u} (Fin 4)) ≤ ULift.up 3 from by decide) := by
  apply SimplicialThickening.Path.ext
  ext x
  obtain ⟨x⟩ := x
  fin_cases x <;> simp [tetrahedronFinalPath, coherentEndpointPath]

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 最初の辺の全区間表示は、元の通常射の頂点の定数族。 -/
lemma tetrahedronInitialTrace_arrow (s : (SimplicialNerve C) _⦋3⦌) :
    tetrahedronInitialTrace s = SSet.const (SimplicialCategory.homEquiv' _ _
      (coherentSimplexArrow s 0 1 (by decide))) := by
  rw [tetrahedronInitialTrace, constantPathParameter_eq_const, SSet.const_comp,
    tetrahedronInitialPath_endpoint]
  simp only [coherentSimplexArrow, Equiv.apply_symm_apply]
  rfl

/-- 最後の辺の全区間表示も、元の通常射の頂点の定数族。 -/
lemma tetrahedronFinalTrace_arrow (s : (SimplicialNerve C) _⦋3⦌) :
    tetrahedronFinalTrace s = SSet.const (SimplicialCategory.homEquiv' _ _
      (coherentSimplexArrow s 2 3 (by decide))) := by
  rw [tetrahedronFinalTrace, constantPathParameter_eq_const, SSet.const_comp,
    tetrahedronFinalPath_endpoint]
  simp only [coherentSimplexArrow, Equiv.apply_symm_apply]
  rfl

/-- 元の通常射の定数族は、単位対象への射と同じ豊穣射の合成。 -/
lemma enrichedFamilyConstant_eq {D : SSet.{u}} {X Y : C} (f : X ⟶ Y) :
    SSet.const (X := D) (SimplicialCategory.homEquiv' X Y f) = toUnit D ≫ eHomEquiv SSet f := by
  have h : eHomEquiv SSet f =
      (SSet.unitHomEquiv _).symm (SimplicialCategory.homEquiv' X Y f) := by
    apply (SSet.unitHomEquiv _).injective
    exact (Equiv.apply_symm_apply _ _).symm
  rw [h]
  rfl

/-- 定数な最初の射との豊穣合成は、元の通常射の前合成。 -/
lemma enrichedFamilyComposition_const_left {D : SSet.{u}} {X Y Z : C}
    (f : X ⟶ Y) (b : D ⟶ SimplicialCategory.sHom Y Z) :
    lift (SSet.const (SimplicialCategory.homEquiv' X Y f)) b ≫ eComp SSet X Y Z =
      b ≫ eHomWhiskerRight SSet f Z := by
  rw [enrichedFamilyConstant_eq]
  dsimp only [eHomWhiskerRight]
  simp only [← Category.assoc]
  congr 1

/-- 定数な最後の射との豊穣合成は、元の通常射の後合成。 -/
lemma enrichedFamilyComposition_const_right {D : SSet.{u}} {X Y Z : C}
    (a : D ⟶ SimplicialCategory.sHom X Y) (g : Y ⟶ Z) :
    lift a (SSet.const (SimplicialCategory.homEquiv' Y Z g)) ≫ eComp SSet X Y Z =
      a ≫ eHomWhiskerLeft SSet X g := by
  rw [enrichedFamilyConstant_eq]
  dsimp only [eHomWhiskerLeft]
  simp only [← Category.assoc]
  congr 1

/-- 第一座標一の辺は、元の零番面の区間の最初の通常射による前合成。 -/
lemma tetrahedronTrace_include_first_whisker (s : (SimplicialNerve C) _⦋3⦌) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
      tetrahedronTrace s = triangleTrace ((SimplicialNerve C).δ 0 s) ≫
        eHomWhiskerRight SSet (coherentSimplexArrow s 0 1 (by decide))
          (s.obj (.mk (ULift.up 3))) := by
  rw [tetrahedronTrace_includeFirst, tetrahedronInitialTrace_arrow]
  exact enrichedFamilyComposition_const_left (coherentSimplexArrow s 0 1 (by decide))
    (triangleTrace ((SimplicialNerve C).δ 0 s))

/-- 第二座標一の辺は、元の三番面の区間の最後の通常射による後合成。 -/
lemma tetrahedronTrace_include_second_whisker (s : (SimplicialNerve C) _⦋3⦌) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
      tetrahedronTrace s = triangleTrace ((SimplicialNerve C).δ 3 s) ≫
        eHomWhiskerLeft SSet (s.obj (.mk (ULift.up 0)))
          (coherentSimplexArrow s 2 3 (by decide)) := by
  rw [tetrahedronTrace_includeSecond, tetrahedronFinalTrace_arrow]
  exact enrichedFamilyComposition_const_right (triangleTrace ((SimplicialNerve C).δ 3 s))
    (coherentSimplexArrow s 2 3 (by decide))

/-- 三単体の最初の元の辺の包含。 -/
def tetrahedronFirstEdgeMap : ⦋1⦌ ⟶ ⦋3⦌ :=
  SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.δ (3 : Fin 4)

/-- 三単体の最後の元の辺の包含。 -/
def tetrahedronLastEdgeMap : ⦋1⦌ ⟶ ⦋3⦌ :=
  SimplexCategory.δ (0 : Fin 3) ≫ SimplexCategory.δ (0 : Fin 4)

end SerrePositivity.KST.SConstruction
