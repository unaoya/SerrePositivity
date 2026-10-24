module

public import SerrePositivity.KST.LocalizingInvariants.StableCospanPullbacks
public import SerrePositivity.InfinityCategories.Core.LimitProjectionExistence
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexIso

/-!
概要：安定圏の任意 cospan の pullback を全単体上で選び、既存の部分族を固定して延長する。
方針：普遍 pullback 四角形を普遍錐と同型にし、全入力の極限の存在で自明射影を得る。
規約：全境界を扱い、入力 cospan と指定した部分の四角形を厳密に保つ。
使われ方：普遍 Ore 四角形の相対高次充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def IsPullbackDiagramVertex {X : SSet.{u}}
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) _⦋0⦌) : Prop :=
  IsPullbackSquare ((functorVertexEquiv (Δ[1] ⊗ Δ[1]) X).symm v)

def pullbackDiagrams (X : SSet.{u}) : SSet.{u} :=
  (fullSubcomplexOnVertices _ (IsPullbackDiagramVertex (X := X)) : SSet.{u})

def squareConeDiagramIso (X : SSet.{u}) :
    (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X ≅
      (ihom (join Δ[0] (horn 2 2 : SSet.{u}))).obj X where
  hom := (pre cospanConeSquareIso.hom).app X
  inv := (pre cospanConeSquareIso.inv).app X
  hom_inv_id := by
    rw [← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id, pre_id]
    rfl
  inv_hom_id := by
    rw [← NatTrans.comp_app, ← pre_map, Iso.hom_inv_id, pre_id]
    rfl

def pullbackDiagramsConesIso (X : SSet.{u}) [Quasicategory X] :
    pullbackDiagrams X ≅ limitCones (horn 2 2 : SSet.{u}) X :=
  fullSubcomplexIso (squareConeDiagramIso X) IsPullbackDiagramVertex
    (TerminalBoundaryLifting (coneRestriction (horn 2 2 : SSet.{u}) X)) (by
      intro v
      obtain ⟨F, rfl⟩ := (functorVertexEquiv (Δ[1] ⊗ Δ[1]) X).surjective v
      change IsPullbackSquare ((functorVertexEquiv _ X).symm (functorVertexEquiv _ X F)) ↔ _
      rw [Equiv.symm_apply_apply]
      exact isLimitCone_iff_terminalBoundaryLifting_coneRestriction (pullbackCone F))

def pullbackProjection (X : SSet.{u}) :
    pullbackDiagrams X ⟶ (ihom (horn 2 2 : SSet.{u})).obj X :=
  (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι ≫ (pre cospanSquareBoundary).app X

lemma pullbackDiagramsConesIso_projection (X : SSet.{u}) [Quasicategory X] :
    (pullbackDiagramsConesIso X).hom ≫ limitConeProjection (horn 2 2 : SSet.{u}) X =
      pullbackProjection X := by
  change ((fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι ≫
    (pre cospanConeSquareIso.hom).app X) ≫ (pre (joinInr Δ[0] (horn 2 2))).app X = _
  rw [Category.assoc, ← NatTrans.comp_app, ← pre_map]
  rfl

instance stable_pullbackProjection_trivialKanFibration (X : SSet.{u})
    [Quasicategory X] [IsStable X] : TrivialKanFibration (pullbackProjection X) := by
  have : TrivialKanFibration (limitConeProjection (horn 2 2 : SSet.{u}) X) :=
    limitConeProjection_trivialKanFibration stable_hasLimit_cospan
  rw [← pullbackDiagramsConesIso_projection]
  exact ⟨trivialKanFibrations.comp_mem _ _ (MorphismProperty.rlp_of_isIso _ _)
    TrivialKanFibration.mem⟩

lemma exists_relative_stable_pullbackFamily {A B X : SSet.{u}} [Quasicategory X] [IsStable X]
    (i : A ⟶ B) [Mono i] (d : B ⟶ (ihom (horn 2 2 : SSet.{u})).obj X)
    (a : A ⟶ pullbackDiagrams X) (ha : a ≫ pullbackProjection X = i ≫ d) :
    ∃ F : B ⟶ pullbackDiagrams X, i ≫ F = a ∧ F ≫ pullbackProjection X = d := by
  have := TrivialKanFibration.mem (p := pullbackProjection X) i inferInstance
  have sq : CommSq a i (pullbackProjection X) d := ⟨ha⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

def stablePullbackSection (X : SSet.{u}) [Quasicategory X] [IsStable X] :
    (ihom (horn 2 2 : SSet.{u})).obj X ⟶ pullbackDiagrams X :=
  Classical.choose (trivialKanFibration_exists_section (pullbackProjection X))

lemma stablePullbackSection_projection (X : SSet.{u}) [Quasicategory X] [IsStable X] :
    stablePullbackSection X ≫ pullbackProjection X = 𝟙 _ :=
  Classical.choose_spec (trivialKanFibration_exists_section (pullbackProjection X))

end SerrePositivity.KST.LocalizingInvariants
