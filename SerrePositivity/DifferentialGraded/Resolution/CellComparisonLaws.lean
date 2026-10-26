module
public import SerrePositivity.DifferentialGraded.Resolution.CycleCoverComparisonLaws
public import SerrePositivity.DifferentialGraded.Resolution.FixedObjectAttachmentLaws
public import SerrePositivity.DifferentialGraded.Resolution.CellComparison

/-!
概要：元の標準 cell 解像度の比較関手は恒等・合成を厳密に保つ。
方針：同じ初期被覆と境界 cell 付加の厳密則を全段階へ帰納し、実余極限で判定する。
規約：通常 dg 射の全 Hom に関する等号。全 native Hom への作用は別工程。
使われ方：D-8 e の同じ分解 cone・実核・懸垂への射作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.DGCategoryCellResolution
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma initialComparison_identity :
    initialComparison A D D (DGFunctor.id D) =
      FixedObjectAugmentation.Map.identity (initial A D) := by
  apply FixedObjectAugmentation.Map.map_ext
  funext x y
  exact eq_of_heq (DGFunctor.hcongr_map (DGCategoryCycleCover.map_identity A D) x y)

lemma stageComparison_identity (n : ℕ) :
    stageComparison A D D (DGFunctor.id D) n =
      FixedObjectAugmentation.Map.identity (stage A D n) := by
  induction n with
  | zero => exact initialComparison_identity A D
  | succ n ih =>
    change (stageComparison A D D (DGFunctor.id D) n).attach = _
    rw [ih, FixedObjectAugmentation.Map.attach_identity]
    rfl

lemma comparisonHom_identity (x y : D) :
    comparisonHom A D D (DGFunctor.id D) x y = 𝟙 (candidateHom A D x y) := by
  apply colimit.hom_ext
  intro n
  change stageInclusion A D n x y ≫ comparisonHom A D D (DGFunctor.id D) x y =
    stageInclusion A D n x y ≫ 𝟙 _
  rw [stageInclusion_comparison]
  have h : (stageComparison A D D (DGFunctor.id D) n).hom x y = 𝟙 _ :=
    congrArg (fun M => M.hom x y) (stageComparison_identity A D n)
  rw [h]
  change 𝟙 _ ≫ stageInclusion A D n x y = stageInclusion A D n x y ≫ 𝟙 _
  simp

lemma comparisonFunctor_identity :
    comparisonFunctor A D D (DGFunctor.id D) = DGFunctor.id (Source A D) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := comparisonFunctor A D D (DGFunctor.id D)) (G := DGFunctor.id (Source A D))
    (fun _ => rfl)
  intro x y
  change comparisonHom A D D (DGFunctor.id D) x.val y.val ≫ eqToHom (by rfl) = 𝟙 _
  rw [eqToHom_refl, Category.comp_id, comparisonHom_identity]

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (B : Type z) [DGCategory A B] [Small.{u} B]

lemma initialComparison_composition (F : DGFunctor A D E) (G : DGFunctor A E B) :
    initialComparison A D B (F.comp G) = FixedObjectAugmentation.Map.composition
      (initialComparison A D E F) (initialComparison A E B G) := by
  apply FixedObjectAugmentation.Map.map_ext
  funext x y
  exact eq_of_heq (DGFunctor.hcongr_map (DGCategoryCycleCover.map_composition A D E B F G) x y)

lemma stageComparison_composition (F : DGFunctor A D E) (G : DGFunctor A E B) (n : ℕ) :
    stageComparison A D B (F.comp G) n = FixedObjectAugmentation.Map.composition
      (stageComparison A D E F n) (stageComparison A E B G n) := by
  induction n with
  | zero => exact initialComparison_composition A D E B F G
  | succ n ih =>
    change (stageComparison A D B (F.comp G) n).attach =
      FixedObjectAugmentation.Map.composition
        (stageComparison A D E F n).attach (stageComparison A E B G n).attach
    rw [ih, FixedObjectAugmentation.Map.attach_composition]

lemma comparisonHom_composition (F : DGFunctor A D E) (G : DGFunctor A E B) (x y : D) :
    comparisonHom A D B (F.comp G) x y =
      comparisonHom A D E F x y ≫ comparisonHom A E B G (F.obj x) (F.obj y) := by
  apply colimit.hom_ext
  intro n
  change stageInclusion A D n x y ≫ comparisonHom A D B (F.comp G) x y =
    stageInclusion A D n x y ≫ (comparisonHom A D E F x y ≫
      comparisonHom A E B G (F.obj x) (F.obj y))
  rw [stageInclusion_comparison, ← Category.assoc, stageInclusion_comparison,
    Category.assoc, stageInclusion_comparison]
  have h : (stageComparison A D B (F.comp G) n).hom x y =
      (stageComparison A D E F n).hom x y ≫
        (stageComparison A E B G n).hom (F.obj x) (F.obj y) :=
    congrArg (fun M => M.hom x y) (stageComparison_composition A D E B F G n)
  rw [h, Category.assoc]
  rfl

lemma comparisonFunctor_composition (F : DGFunctor A D E) (G : DGFunctor A E B) :
    comparisonFunctor A D B (F.comp G) =
      (comparisonFunctor A D E F).comp (comparisonFunctor A E B G) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := comparisonFunctor A D B (F.comp G))
    (G := (comparisonFunctor A D E F).comp (comparisonFunctor A E B G)) (fun _ => rfl)
  intro x y
  change comparisonHom A D B (F.comp G) x.val y.val ≫ eqToHom (by rfl) =
    comparisonHom A D E F x.val y.val ≫ comparisonHom A E B G (F.obj x.val) (F.obj y.val)
  rw [eqToHom_refl, Category.comp_id, comparisonHom_composition]

end SerrePositivity.DifferentialGraded.DGCategoryCellResolution
