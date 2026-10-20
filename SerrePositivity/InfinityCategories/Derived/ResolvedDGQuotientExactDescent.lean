module
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientLocalization
/-!
概要：平坦分解後の実商からの延長の完全性を反映する。
方針：増大と商の同じ関手同型に沿い、平坦商での完全性反映を使う。
規約：元の Hom の平坦性を仮定しない。使われ方：一般の Verdier 列の完全関手普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
/-- 平坦分解後の商からの実関手は、元の dg nerve への制限が完全なら完全。 -/
lemma resolvedDGQuotient_isExactFunctor_of_precomp (P : Set D) {Y : SSet.{max u v}}
    [Quasicategory Y] (G : resolvedDGQuotientNerve A D P ⟶ Y)
    [IsExactFunctor (resolvedDGQuotientFunctor A D P ≫ G)] : IsExactFunctor G := by
  let := dgCellResolutionSource_isDGPretriangulated A D
  let E := dgNerve.map (DGCategoryCellResolution.augmentation A D)
  have : IsExactFunctor E :=
    isExactFunctor_of_isQCatEquivalence (dgCellAugmentationNerve_isQCatEquivalence A D)
  have h : IsExactFunctor ((E ≫ resolvedDGQuotientFunctor A D P) ≫ G) := by
    simpa only [Category.assoc] using isExactFunctor_comp E (resolvedDGQuotientFunctor A D P ≫ G)
  have hp : IsExactFunctor (resolvedDGQuotientProjection A D P ≫ G) :=
    isExactFunctor_of_functorIso ((resolvedDGQuotientRoofIso A D P).postcomp G)
  change IsExactFunctor (dgQuotientNerveProjection A (DGCategoryCellResolution.Source A D)
    (resolvedDGNullObjects A D P) ≫ G) at hp
  exact dgQuotient_isExactFunctor_of_precomp A (DGCategoryCellResolution.Source A D)
    (resolvedDGNullObjects A D P) (resolvedDGQuotient_localKFlat A D P) G
/-- 元の指定対象を零化する完全関手は、平坦商上の完全な実延長同型を持つ。 -/
lemma resolvedDGVerdierExactFunctor_extension_exists (P : Set D) {Y : SSet.{max u v}}
    [Quasicategory Y] [IsStable Y] (F : dgNerve A D ⟶ Y) [IsExactFunctor F]
    (hF : ∀ b : P, IsZeroVertex (F.app (Opposite.op ⦋0⦌) (Simplex.vertex b.val))) :
    ∃ G : resolvedDGQuotientNerve A D P ⟶ Y, IsExactFunctor G ∧
      Nonempty (FunctorIso (resolvedDGQuotientFunctor A D P ≫ G) F) := by
  obtain ⟨G, ⟨e⟩⟩ := resolvedDGVerdierFunctor_extension_exists A D P F
    ((dgVerdierEdges_inverts_iff_kills A D F P).mpr hF)
  have : IsExactFunctor (resolvedDGQuotientFunctor A D P ≫ G) :=
    isExactFunctor_of_functorIso e.symm
  exact ⟨G, resolvedDGQuotient_isExactFunctor_of_precomp A D P G, ⟨e⟩⟩
end SerrePositivity.InfinityCategories
