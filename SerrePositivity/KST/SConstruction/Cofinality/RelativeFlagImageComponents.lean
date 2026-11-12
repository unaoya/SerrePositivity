module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagDiagonalEvaluation

/-!
概要：同じ全多次数の wide 成分内で元の指定射の本質像所属を輸送する。
方針：分母の cofiber の三角形の二対三性を使い、元の π₀ の生成関係に沿って移す。
規約：本質像を retract 閉包へ広げない。
使われ方：相対旗の零成分と元の始域の図式の照合。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：同じ反復 S の分母辺の両端で元の本質像所属は同値。
方針：実分母を三角的分母へ移し、同じ三角形の閉性を両方向に使う。
規約：元の指定射の本質像を結論に保持する。
使われ方：wide 成分内の零成分条件の輸送。 -/
lemma completionMultiWideEdge_image_iff (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    {x y : (((multiSEndofunctor r).obj ι).obj Y).carrier _⦋0⦌}
    (a : Truncated.Edge (X := (truncation 2).obj
      (((multiSEndofunctor r).obj ι).obj Y).carrier) x y)
    (ha : a.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val)) :
    x ∈ LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val ↔
      y ∈ LocalizingInvariants.completionEssentialImage
        (((multiSEndofunctor r).obj ι).map f).val := by
  let F := ((multiSEndofunctor r).obj ι).map f
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F.val := stableModelHom_exact F
  let P := LocalizingInvariants.completionEssentialImage F.val
  have he := LocalizingInvariants.stableClosure_completionEssentialImage F.val
    (multiSEndofunctor_map_isIdempotentCompletion r ι f hf).2.1
  have hm (z) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P z ↔ z ∈ P :=
    Iff.of_eq (congrArg (fun Q => z ∈ Q) he)
  have hw := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_iff_trW P a).mp (he.symm ▸ ha)
  obtain ⟨Z, g, h, hT, hZ⟩ := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure P).trW_iff _ |>.mp hw
  constructor
  · intro hx
    exact (hm y).mp ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure P).ext_of_isTriangulatedClosed₂ _ hT ((hm x).mpr hx) hZ)
  · intro hy
    exact (hm x).mp ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure P).ext_of_isTriangulatedClosed₁ _ hT ((hm y).mpr hy) hZ)

/-- 概要：同じ全多次数の wide の同じ成分内では元の本質像所属が一致する。
方針：元の辺の関係・反射・対称・推移に沿って両端の同値を合成する。
規約：成分を K₀ の商と未証明のまま同一視しない。
使われ方：相対旗の基点成分から始域の全図式への回収。 -/
lemma completionMultiWideComponent_image_iff (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (x y : (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) _⦋0⦌)
    (hxy : SSet.π₀.mk x = SSet.π₀.mk y) :
    x.val ∈ LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val ↔
      y.val ∈ LocalizingInvariants.completionEssentialImage
        (((multiSEndofunctor r).obj ι).map f).val := by
  have hp := (SSet.π₀.mk_eq_mk_iff x y).mp hxy
  clear hxy
  induction hp with
  | rel a b hab =>
    obtain ⟨e⟩ := hab
    apply completionMultiWideEdge_image_iff r ι f hf
      (e.map (LocalizingInvariants.completionCofiberWide
        (((multiSEndofunctor r).obj ι).map f).val).ι).toTruncated
    change e.edge.val ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val)
    simpa only [op_id, CategoryTheory.Functor.map_id, types_id_apply]
      using e.edge.property (𝟙 ⦋1⦌)
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end SerrePositivity.KST.SConstruction.Cofinality
