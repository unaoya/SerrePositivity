module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionKMap

/-!
概要：同じ増大可換データの懸垂入力射が、元の ε を保ち恒等・合成と整合する。
方針：D 正本の指定収縮付き普遍性を、同じ K-B の実射データへ特殊化する。
規約：一般の商関手則を再定義せず、canonical cell 比較の恒等・合成則は別の供給境界。
使われ方：明示した同じ cone・平坦分解の実射に沿う懸垂の厳密整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ明示射データの恒等懸垂入力射は、元の厳密な恒等射。 -/
theorem dgKappaSuspensionInputMap_id :
    dgKappaSuspensionInputMap R D D I I (DGKappaSuspensionMapData.id R D I) =
      𝟙 (dgKappaSuspensionKInput R D I) := by
  let C₀ := DGCategoryCellResolution.Source R (DGKappaCone R D I)
  let S₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)
  apply ULift.ext
  change DGQuotient.quotientDGFunctor R C₀ C₀ (DGFunctor.id C₀) S₀ S₀ _ = DGFunctor.id _
  apply (DGQuotient.universalEquiv R C₀ S₀ (DGQuotient.QuotientObject C₀ S₀)).injective
  change DGQuotient.restrictContractedFunctor R C₀ S₀ (DGQuotient.extension R _) = _
  rw [DGQuotient.restrict_extension]
  apply DGQuotient.ContractedFunctor.ext R
  · change (DGFunctor.id C₀).comp (DGQuotient.inclusion R C₀ S₀) =
      (DGQuotient.inclusion R C₀ S₀).comp (DGFunctor.id _)
    rw [strictDGFunctor_id_comp, strictDGFunctor_comp_id]
  · exact heq_of_eq (funext (fun _ => rfl))

variable (E F : Type v) [DGCategory R E] [DGCategory R F] [Small.{u} E] [Small.{u} F]
  (J : DGKappaConeInput R E κ) (K : DGKappaConeInput R F κ)
  (M : DGKappaSuspensionMapData R D E I J) (N : DGKappaSuspensionMapData R E F J K)

/-- 元の懸垂入力射は、商の同じ標準 ε を全次数 −1 の元として厳密に保持する。 -/
theorem dgKappaSuspensionInputMap_epsilon
    (b : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)) :
    (((dgKappaSuspensionInputMap R D E I J M).down.map ⟨b.val⟩ ⟨b.val⟩).f (-1)
      (DGQuotient.epsilonElement R (DGCategoryCellResolution.Source R (DGKappaCone R D I))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)) b)) =
      DGQuotient.epsilonElement R (DGCategoryCellResolution.Source R (DGKappaCone R E J))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R E J) (dgKappaConePerfectObjects R E J))
        ⟨M.resolved.obj b.val,
          dgKappaSuspensionMap_preservesNullObjects R D E I J M b.val b.property⟩ :=
  DGQuotient.quotientDGFunctor_epsilon R _ _ _ _ _ _ b

/-- 元の明示した実射データの合成は、同じ ε を保つ懸垂入力射の厳密合成に移る。 -/
theorem dgKappaSuspensionInputMap_comp :
    dgKappaSuspensionInputMap R D F I K (DGKappaSuspensionMapData.comp R D E I J M N) =
      dgKappaSuspensionInputMap R D E I J M ≫ dgKappaSuspensionInputMap R E F J K N := by
  let C₀ := DGCategoryCellResolution.Source R (DGKappaCone R D I)
  let C₁ := DGCategoryCellResolution.Source R (DGKappaCone R E J)
  let C₂ := DGCategoryCellResolution.Source R (DGKappaCone R F K)
  let S₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)
  let S₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R E J) (dgKappaConePerfectObjects R E J)
  let S₂ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R F K) (dgKappaConePerfectObjects R F K)
  let qM := DGQuotient.quotientDGFunctor R C₀ C₁ M.resolved S₀ S₁
    (dgKappaSuspensionMap_preservesNullObjects R D E I J M)
  let qN := DGQuotient.quotientDGFunctor R C₁ C₂ N.resolved S₁ S₂
    (dgKappaSuspensionMap_preservesNullObjects R E F J K N)
  apply ULift.ext
  change DGQuotient.quotientDGFunctor R C₀ C₂ (M.resolved.comp N.resolved) S₀ S₂ _ = qM.comp qN
  apply (DGQuotient.universalEquiv R C₀ S₀ (DGQuotient.QuotientObject C₂ S₂)).injective
  change DGQuotient.restrictContractedFunctor R C₀ S₀ (DGQuotient.extension R _) =
    DGQuotient.restrictContractedFunctor R C₀ S₀ (qM.comp qN)
  rw [DGQuotient.restrict_extension, DGQuotient.restrictContractedFunctor_comp]
  have hM : DGQuotient.restrictContractedFunctor R C₀ S₀ qM =
      DGQuotient.functorContracted R C₀ C₁ M.resolved S₀ S₁
        (dgKappaSuspensionMap_preservesNullObjects R D E I J M) :=
    DGQuotient.restrict_extension R _
  rw [hM]
  apply DGQuotient.ContractedFunctor.ext R
  · change (M.resolved.comp N.resolved).comp (DGQuotient.inclusion R C₂ S₂) =
      (M.resolved.comp (DGQuotient.inclusion R C₁ S₁)).comp qN
    rw [strictDGFunctor_comp_assoc, strictDGFunctor_comp_assoc,
      DGQuotient.quotientDGFunctor_inclusion]
  · apply heq_of_eq
    funext b
    exact (DGQuotient.quotientDGFunctor_epsilon R C₁ C₂ N.resolved S₁ S₂
      (dgKappaSuspensionMap_preservesNullObjects R E F J K N)
      ⟨M.resolved.obj b.val,
        dgKappaSuspensionMap_preservesNullObjects R D E I J M b.val b.property⟩).symm

end SerrePositivity.KST.NonConnective
