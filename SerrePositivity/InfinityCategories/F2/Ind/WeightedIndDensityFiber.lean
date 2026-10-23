module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndDensityCocone
public import SerrePositivity.InfinityCategories.F1.Universe.WeightedTransport

/-!
概要：weighted 密度図式の同じ添字 fiber は、元の各 right fibration 全空間の密度図式。
方針：元の weighted fiber 同型を宇宙移送し、同じ底への射影と Yoneda の合成を計算する。
規約：全単体の射の厳密な一致。使われ方：点ごとの密度余錐を全相対 join 図式へ束ねる入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [PartialOrder I] [CategoryTheory.IsFiltered I] [IsCardinalFiltered I κ]
  (F : I ⥤ RightFibrationObject C) [∀ i, IsKappaFiltered κ (F.obj i).val.left]

omit [Quasicategory C] [CategoryTheory.IsFiltered I] [Fact κ.IsRegular]
  [IsCardinalFiltered I κ] [∀ i, IsKappaFiltered κ (F.obj i).val.left] in
/-- 同じ weighted 底射影の各係数への制限は、元の right fibration の射影。 -/
lemma weightedIndDensityBase_coefficient (i : I) :
    weightedNerveConstantLift (rightFibrationTotalDiagram F) i ≫ weightedIndDensityBase F =
      (F.obj i).val.hom := by
  unfold weightedIndDensityBase
  rw [← strictRightFibrationTotalAssembly_projection, ← Category.assoc,
    strictRightFibrationTotalAssembly_coefficient, strictRightFibrationColimitProjection_ι]

omit [Quasicategory C] [CategoryTheory.IsFiltered I] [Fact κ.IsRegular]
  [IsCardinalFiltered I κ] [∀ i, IsKappaFiltered κ (F.obj i).val.left] in
/-- 元の fiber 同型の全空間への包含は、元の係数包含をそのまま持ち上げた射。 -/
lemma uliftWeightedIndDensityFiberIso_ι (i : I) :
    (uliftWeightedNerveFiberIso.{u, u + 1} (rightFibrationTotalDiagram F) i).hom ≫
      vertexFiberι ((SSet.uliftFunctor.{u + 1, u}).map
        (weightedNerveProjection (rightFibrationTotalDiagram F))) (ULift.up (nerveVertex i)) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (weightedNerveConstantLift (rightFibrationTotalDiagram F) i) := by
  rw [uliftWeightedNerveFiberIso, Iso.trans_hom, Category.assoc, uliftVertexFiberIso_hom_ι,
    CategoryTheory.Functor.mapIso_hom,
    ← CategoryTheory.Functor.map_comp]
  change (SSet.uliftFunctor.{u + 1, u}).map
    (weightedNerveFiberMap (rightFibrationTotalDiagram F) i ≫ vertexFiberι _ _) = _
  rw [weightedNerveFiberMap, vertexFiberLift_ι]

omit [Fact κ.IsRegular] [IsCardinalFiltered I κ] [∀ i, IsKappaFiltered κ (F.obj i).val.left] in
/-- 元の weighted fiber 図式を同じ元の全空間で読むと、元の射影による密度図式そのもの。 -/
lemma weightedIndDensityFiber_diagram (i : I) :
    (uliftWeightedNerveFiberIso.{u, u + 1} (rightFibrationTotalDiagram F) i).hom ≫
      (vertexFiberι ((SSet.uliftFunctor.{u + 1, u}).map
        (weightedNerveProjection (rightFibrationTotalDiagram F))) (ULift.up (nerveVertex i)) ≫
          weightedIndDensityDiagram κ F) =
      (SSet.uliftFunctor.{u + 1, u}).map (F.obj i).val.hom ≫ indYoneda κ C := by
  rw [← Category.assoc, uliftWeightedIndDensityFiberIso_ι, weightedIndDensityDiagram,
    ← Category.assoc, ← CategoryTheory.Functor.map_comp, weightedIndDensityBase_coefficient]

omit [Fact κ.IsRegular] [IsCardinalFiltered I κ] in
/-- 同じ weighted 密度図式は各元の添字 fiber 上で native な余極限を持つ。 -/
lemma weightedIndDensityFiber_hasColimit (i : I) :
    HasColimit (vertexFiberι ((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveProjection (rightFibrationTotalDiagram F))) (ULift.up (nerveVertex i)) ≫
        weightedIndDensityDiagram κ F) := by
  apply (hasColimit_iff_restrict_of_precompositionEquivalence _ _
    (isPrecompositionEquivalence_of_iso
      (uliftWeightedNerveFiberIso.{u, u + 1} (rightFibrationTotalDiagram F) i))).mpr
  rw [weightedIndDensityFiber_diagram]
  exact ⟨rightClassifiedIndDensityCocone κ (F.obj i),
    rightClassifiedIndDensityCocone_isColimit κ (F.obj i)⟩

omit [Fact κ.IsRegular] [IsCardinalFiltered I κ] in
/-- 元の添字の全頂点について、同じ fiber 図式の native な余極限が存在する。 -/
lemma weightedIndDensity_allFibers_hasColimit
    (v : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) _⦋0⦌) :
    HasColimit (vertexFiberι ((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveProjection (rightFibrationTotalDiagram F))) v ≫ weightedIndDensityDiagram κ F) := by
  obtain ⟨v⟩ := v
  obtain ⟨i, rfl⟩ := nerveEquiv.symm.surjective v
  exact weightedIndDensityFiber_hasColimit κ F i

end SerrePositivity.InfinityCategories.F2.Ind
