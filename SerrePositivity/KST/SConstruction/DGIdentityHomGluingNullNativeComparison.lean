module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingNullArrow
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityHomTargetDiagonal

/-!
概要：V の元包含を元恒等対角と native 全関手同型で比較する。
方針：元 augmented 矢印全族を Sp 正本の可逆矢印族比較へ渡す。
規約：固定 S の厳密関手 Hom end の同型とは同一視しない。
使われ方：元実零化面と恒等対角零化面の ν 全比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type (u + 1)) [DGCategory R C] [Small.{u} C]
local notation "I" => DGFunctor.id C
local notation "M" => dgHomGluingBimodule R C C C (I) (I)
local notation "L" => DGIdentityHomGluing R C
local notation "V" => DGIdentityHomGluingNullDomain R C
local notation "j" => dgIdentityHomGluingNullInclusion R C
/-- 概要：固定宇宙の元恒等 Hom gluing の D2 全比較。
方針：供給済み比較を同じ小基底へ特殊化する。
規約：元全 Hom と宇宙を固定。使われ方：V の native 全比較の反映先。 -/
abbrev dgIdentityHomGluingNullLaxEquivalence :=
  dgGluingIdentityHomTargetLaxEquivalence.{u, 0} R C
local notation "E" => dgIdentityHomGluingNullLaxEquivalence R C
local notation "a" => (dgNerve.map (j) ≫ QCatEquivalence.hom (E)) ≫
  F2.laxPullbackArrow (𝟙 (dgNerve R C)) (𝟙 (dgNerve R C))

/-- 概要：V の元左成分への厳密 dg 射影。
方針：元包含と元 gluing 射影を合成する。
規約：元全 Hom を保持。使われ方：元対角側の native 全比較。 -/
def dgIdentityHomGluingNullProjection : DGFunctor R (V) C :=
  (j).comp (dgGluingLeft R C C (M))

/-- 概要：V 上の元 augmented 矢印全族は可逆矢印の空間に入る。
方針：元 cone 可縮性から同じ元閉辺の可逆性を適用する。
規約：元全族を変更しない。使われ方：Sp 正本の全族比較の入力。 -/
lemma dgIdentityHomGluingNull_arrow_vertices :
    ∀ x, IsEquivalencePathVertex ((a).app (Opposite.op ⦋0⦌) x) := by
  intro x
  obtain ⟨x, rfl⟩ := (dgNerve.vertexEquiv R (V)).symm.surjective x
  change IsEquivalencePathVertex
    ((dgNerve.map (j) ≫ (E).hom ≫
      F2.laxPullbackArrow (𝟙 (dgNerve R C)) (𝟙 (dgNerve R C))).app _ _)
  rw [dgGluingIdentityHomTargetLaxEquivalence_arrow]
  change IsEquivalencePathVertex
    ((dgGluingHomTargetAugmentationArrowFamily.{u, 0} R C C C (I) (I)).app _
      (DGNerve.Simplex.vertex x.val))
  unfold IsEquivalencePathVertex
  rw [dgGluingIdentityAugmentation_vertex.{u, 0}]
  exact (isInvertibleEdge_congr (by rfl)).mp
    (dgIdentityHomGluingNullProperty_targetEdgeInvertible R C x.val x.property)

/-- 概要：V の元包含の lax 全像は始点の恒等矢印全族と全比較される。
方針：元可逆矢印全族に Sp 正本の比較を適用して元 lax 逆で戻す。
規約：全パラメーターを保持。使われ方：元恒等対角側との native 全比較。 -/
def dgIdentityHomGluingNull_laxComparison : FunctorIso
    (dgNerve.map (j) ≫ (E).hom)
    ((dgNerve.map (j) ≫ dgNerve.map (dgGluingLeft R C C (M))) ≫
      constantFunctorMap (Δ[1] : SSet) (dgNerve R C) ≫ _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.arrowLaxInverse (dgNerve R C)) := by
  let e := FunctorIso.postcomp
    (EquivalenceArrowFamily.comparison (a) (dgIdentityHomGluingNull_arrow_vertices R C))
    (_root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.arrowLaxInverse (dgNerve R C))
  have hs : (a) ≫ _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.arrowLaxInverse (dgNerve R C) = dgNerve.map (j) ≫ (E).hom := by
    change ((dgNerve.map (j) ≫ (E).hom) ≫ (_root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.arrowLaxIso (dgNerve R C)).hom) ≫
      (_root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.arrowLaxIso (dgNerve R C)).inv = _
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have ht : (a) ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      dgNerve.map (j) ≫ dgNerve.map (dgGluingLeft R C C (M)) := by
    simp only [Category.assoc, F2.laxPullbackArrow_source, Category.comp_id]
    rw [dgGluingIdentityHomTargetLaxEquivalence_fst]
  exact F2.functorIsoOfEq e hs (by rw [ht]; exact Category.assoc _ _ _)

/-- 概要：V の元包含は元射影の後の恒等対角と native 全関手同型。
方針：同じ lax 全比較を元対角の全比較に貼り、元全写像空間同値で反映する。
規約：元三つの厳密関手を保持。使われ方：V と恒等対角の ν 全面比較。 -/
def dgIdentityHomGluingNullNativeComparison : FunctorIso
    (dgNerve.map (j))
    (dgNerve.map (dgIdentityHomGluingNullProjection R C) ≫
      dgNerve.map (dgIdentityHomGluingDiagonal R C)) := by
  let p := dgNerve.map (dgIdentityHomGluingNullProjection R C)
  let c := constantFunctorMap (Δ[1] : SSet) (dgNerve R C)
  let b := _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.arrowLaxInverse (dgNerve R C)
  have hp : dgNerve.map (j) ≫ dgNerve.map (dgGluingLeft R C C (M)) = p :=
    (dgNerve.map_comp _ _).symm
  have e₀ : FunctorIso (dgNerve.map (j) ≫ (E).hom) (p ≫ c ≫ b) := by
    exact F2.functorIsoOfEq (dgIdentityHomGluingNull_laxComparison R C) rfl
      (by rw [hp])
  have e₁ : FunctorIso
      ((p ≫ dgNerve.map (dgIdentityHomGluingDiagonal R C)) ≫ (E).hom)
      (p ≫ c ≫ b) := by
    exact F2.functorIsoOfEq
      (FunctorIso.precomp (dgGluingIdentityNativeDiagonalIso.{u, 0} R C) p)
      (Category.assoc _ _ _).symm rfl
  exact (E).isQCatEquivalence.isFullyFaithful.preimageFunctorIso (e₀.trans e₁.symm)

end SerrePositivity.KST.SConstruction
