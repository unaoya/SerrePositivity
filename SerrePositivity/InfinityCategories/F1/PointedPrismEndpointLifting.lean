module

public import SerrePositivity.InfinityCategories.F1.PointedPrismEvaluation
public import SerrePositivity.InfinityCategories.F1.PrismBoundaryLifting

/-!
概要：全 pointed-space lift 空間の同時端点制限の相対持ち上げ。
方針：底の区間を先に延長し、二端点を指定した prism を延長して全 lift 空間へ戻す。
規約：始点写像は同値に制限しない。
使われ方：同時端点制限の left fibration と Kan fibration 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories


/-- 概要：区間と境界の相対内部 Hom の持ち上げ性から同時端点制限の持ち上げ性を得る。
方針：区間を延長し、両端を貼り合わせて prism を充填する。
規約：パラメーター射 i は任意。
使われ方：実際の同時端点制限の左ホーン充填の共通部分。 -/
lemma hasLiftingProperty_pointedPrismLiftEndpoints {K T U : SSet.{u + 1}}
    (s t : SpaceInfinity.{u} _⦋0⦌) (i : T ⟶ U)
    (r : internalHom.PullbackObjObj ((boundary 1).ι ▷ K) pointedSpaceProjection)
    [HasLiftingProperty i r.π]
    (hI : ∀ a : T ⟶ intervalMappingSpace s t,
      ∃ q : U ⟶ intervalMappingSpace s t, i ≫ q = a) :
    HasLiftingProperty i (pointedPrismLiftEndpoints K s t) := by
  constructor
  intro a b sq
  let P := pointedPrismLiftParameters K s t
  let C := prismLiftSpaceCurry pointedSpaceProjection K (pointedPrismData K s t)
  let J := prismLiftSpacePrism pointedSpaceProjection K (pointedPrismData K s t)
  have J₀ : prismEndpoint 0 (K ⊗ pointedPrismLiftSpace K s t) ≫ J =
      uncurry (pointedPrismLiftSource K s t) ≫ vertexFiberι pointedSpaceProjection s :=
    pointedPrismEvaluation_zero K s t
  have J₁ : prismEndpoint 1 (K ⊗ pointedPrismLiftSpace K s t) ≫ J =
      uncurry (pointedPrismLiftEndpoint K s t) ≫ vertexFiberι pointedSpaceProjection t :=
    pointedPrismEvaluation_one K s t
  have hs : a ≫ pointedPrismLiftSource K s t = i ≫ b ≫ fst _ _ := by
    have h := congrArg (fun w ↦ w ≫ fst _ _) sq.w
    simpa only [Category.assoc, pointedPrismLiftEndpoints, lift_fst] using h
  have ht : a ≫ pointedPrismLiftEndpoint K s t = i ≫ b ≫ snd _ _ := by
    have h := congrArg (fun w ↦ w ≫ snd _ _) sq.w
    simpa only [Category.assoc, pointedPrismLiftEndpoints, lift_snd] using h
  obtain ⟨q, hq⟩ := hI (a ≫ P ≫ snd _ _)
  let v₀ := uncurry (b ≫ fst _ _) ≫ vertexFiberι pointedSpaceProjection s
  let v₁ := uncurry (b ≫ snd _ _) ≫ vertexFiberι pointedSpaceProjection t
  let δ := (Δ[1] ◁ snd K U) ≫ intervalMappingUncurry q
  have h₀ : v₀ ≫ pointedSpaceProjection = prismEndpoint 0 _ ≫ δ := by
    dsimp only [v₀, δ]
    rw [Category.assoc, vertexFiberι_comp, ← Category.assoc, prismEndpoint_naturality,
      Category.assoc, intervalMappingUncurry_zero, SSet.comp_const, SSet.comp_const]
  have h₁ : v₁ ≫ pointedSpaceProjection = prismEndpoint 1 _ ≫ δ := by
    dsimp only [v₁, δ]
    rw [Category.assoc, vertexFiberι_comp, ← Category.assoc, prismEndpoint_naturality,
      Category.assoc, intervalMappingUncurry_one, SSet.comp_const, SSet.comp_const]
  let A := (Δ[1] ◁ (K ◁ a)) ≫ J
  have A₀ : prismEndpoint 0 _ ≫ A = (K ◁ i) ≫ v₀ := by
    change prismEndpoint 0 _ ≫ (Δ[1] ◁ (K ◁ a)) ≫ J = _
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, J₀]
    dsimp only [v₀]
    rw [← Category.assoc, ← uncurry_natural_left, hs, uncurry_natural_left, Category.assoc]
  have A₁ : prismEndpoint 1 _ ≫ A = (K ◁ i) ≫ v₁ := by
    change prismEndpoint 1 _ ≫ (Δ[1] ◁ (K ◁ a)) ≫ J = _
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, J₁]
    dsimp only [v₁]
    rw [← Category.assoc, ← uncurry_natural_left, ht, uncurry_natural_left, Category.assoc]
  have Ap : A ≫ pointedSpaceProjection = (Δ[1] ◁ (K ◁ i)) ≫ δ := by
    calc
      _ = (Δ[1] ◁ snd K T) ≫ intervalMappingUncurry (a ≫ P ≫ snd _ _) := by
        dsimp only [A, J, P]
        rw [Category.assoc, pointedPrismEvaluation_base, intervalMappingUncurry_precomp]
        rfl
      _ = _ := by rw [← hq, intervalMappingUncurry_precomp]; rfl
  obtain ⟨H, hH, H₀, H₁, Hp⟩ := exists_prismBoundaryLift
    pointedSpaceProjection r i v₀ v₁ δ h₀ h₁ A A₀ A₁ Ap
  let g : U ⟶ pointedPrismParameterSpace K s t := lift (b ≫ fst _ _) q
  have Hg₀ : prismEndpoint 0 _ ≫ H = (K ◁ g) ≫ pointedPrismInitial K s t := by
    rw [pointedPrismInitial_precomp]
    simpa only [g, lift_fst] using H₀
  have Hgp : H ≫ pointedSpaceProjection = (Δ[1] ◁ (K ◁ g)) ≫ pointedPrismBase K s t := by
    rw [pointedPrismBase_precomp]
    simpa only [g, lift_snd] using Hp
  let L := prismLiftSpaceLift pointedSpaceProjection (pointedPrismInitial K s t)
    (pointedPrismBase K s t) (pointedPrismInitial_base K s t) g H Hg₀ Hgp
  have hLP : L ≫ P = g := prismLiftSpaceLift_projection _ _ _ _ _ _ _ _
  have hLC : L ≫ C = curry ((α_ Δ[1] K U).hom ≫ H) :=
    prismLiftSpaceLift_curry _ _ _ _ _ _ _ _
  have hLJ : (Δ[1] ◁ (K ◁ L)) ≫ J = H := prismLiftSpaceLift_prism _ _ _ _ _ _ _ _
  refine CommSq.HasLift.mk' { l := L, fac_left := ?_, fac_right := ?_ }
  · apply prismLiftSpace_hom_ext pointedSpaceProjection (pointedPrismData K s t)
    · change (i ≫ L) ≫ C = a ≫ C
      rw [Category.assoc, hLC, ← curry_natural_left]
      apply uncurry_injective
      rw [uncurry_curry, uncurry_natural_left]
      change (α_ Δ[1] K T).hom ≫ ((Δ[1] ◁ (K ◁ i)) ≫ H) =
        (α_ Δ[1] K T).hom ≫ A
      rw [hH]
    · change (i ≫ L) ≫ P = a ≫ P
      rw [Category.assoc, hLP]
      apply CartesianMonoidalCategory.hom_ext
      · simpa only [Category.assoc, g, lift_fst, P, pointedPrismLiftSource] using hs.symm
      · simpa only [Category.assoc, g, lift_snd] using hq
  · apply CartesianMonoidalCategory.hom_ext
    · change L ≫ pointedPrismLiftSource K s t = b ≫ fst _ _
      change (L ≫ P) ≫ fst _ _ = _
      rw [hLP]
      exact lift_fst _ _
    · change L ≫ pointedPrismLiftEndpoint K s t = b ≫ snd _ _
      apply uncurry_injective
      apply vertexFiber_hom_ext pointedSpaceProjection t
      rw [uncurry_natural_left, Category.assoc, ← J₁]
      calc
        _ = prismEndpoint 1 _ ≫ (Δ[1] ◁ (K ◁ L)) ≫ J := by
          simpa only [Category.assoc] using congrArg (fun w ↦ w ≫ J)
            (prismEndpoint_naturality 1 (K ◁ (show U ⟶ pointedPrismLiftSpace K s t from L))).symm
        _ = _ := (congrArg (fun w ↦ prismEndpoint 1 _ ≫ w) hLJ).trans H₁

end SerrePositivity.InfinityCategories
