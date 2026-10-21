module

public import SerrePositivity.KST.LocalizingInvariants.FixedTargetFinalHorn
public import SerrePositivity.KST.LocalizingInvariants.ArrowPullbackCartesianEdge
public import SerrePositivity.InfinityCategories.Stable.SpanFamilies

/-!
概要：右脚が cartesian な span の最終外ホーンを第一終点を固定して延長する。
方針：右脚を先に充填し、その始点図式の上で定値終点の左脚を充填して貼る。
規約：分母はまだ課さない。使われ方：分母付き span 族への全頂点での持ち上げ。
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

lemma spanArrowFamily_source_eq {A X : SSet.{u}}
    (F : A ⟶ (ihom (horn 2 0 : SSet.{u})).obj X) :
    F ≫ (pre horn₂₀.ι₀₁).app X ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
    F ≫ (pre horn₂₀.ι₀₂).app X ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [stable_pre_evaluateFunctorAt, stable_pre_evaluateFunctorAt]
  rfl

lemma exists_span_finalHorn_extension_of_right_cartesian
    {X : SSet.{u}} [Quasicategory X] (m : ℕ)
    (σ : (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) ⟶
      (ihom (horn 2 0 : SSet.{u})).obj X)
    (β : (Δ[m + 2] : SSet.{u}) ⟶ X) (x : X _⦋0⦌)
    (hs : σ ≫ (pre horn₂₀.ι₀₁).app X ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = SSet.const x)
    (ht : σ ≫ (pre horn₂₀.ι₀₂).app X ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      (horn (m + 2) (Fin.last (m + 2))).ι ≫ β)
    (hc : IsCartesianEdge (evaluateFunctorAt (Y := X)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      ((σ ≫ (pre horn₂₀.ι₀₂).app X).app (Opposite.op ⦋1⦌) (finalHornEdge m))) :
    ∃ G : (Δ[m + 2] : SSet.{u}) ⟶ (ihom (horn 2 0 : SSet.{u})).obj X,
      (horn (m + 2) (Fin.last (m + 2))).ι ≫ G = σ ∧
      G ≫ (pre horn₂₀.ι₀₁).app X ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = SSet.const x ∧
      G ≫ (pre horn₂₀.ι₀₂).app X ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = β := by
  let sq : CommSq (σ ≫ (pre horn₂₀.ι₀₂).app X)
      (horn (m + 2) (Fin.last (m + 2))).ι
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) β := ⟨ht⟩
  have := hc m (σ ≫ (pre horn₂₀.ι₀₂).app X) β rfl sq
  let R := sq.lift
  have hR : (horn (m + 2) (Fin.last (m + 2))).ι ≫ R =
      σ ≫ (pre horn₂₀.ι₀₂).app X := sq.fac_left
  have hRt : R ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = β := sq.fac_right
  have hLs : (σ ≫ (pre horn₂₀.ι₀₁).app X) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      (horn (m + 2) (Fin.last (m + 2))).ι ≫
        (R ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
    rw [← Category.assoc, hR, Category.assoc, Category.assoc]
    exact spanArrowFamily_source_eq σ
  obtain ⟨L, hL, hLb⟩ := exists_fixedTarget_finalHorn_extension m
    (σ ≫ (pre horn₂₀.ι₀₁).app X)
    (R ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) x hLs
    (by simpa only [Category.assoc] using hs)
  have hLR := interval_source_of_boundary_diagram L _ _ hLb
  let G := stable_spanFamilyOfArrows L R hLR
  have hGl : G ≫ (pre horn₂₀.ι₀₁).app X = L := stable_spanFamilyOfArrows_left _ _ _
  have hGr : G ≫ (pre horn₂₀.ι₀₂).app X = R := stable_spanFamilyOfArrows_right _ _ _
  refine ⟨G, ?_, ?_, ?_⟩
  · apply stable_spanFamily_hom_ext
    · rw [Category.assoc, hGl]
      exact hL
    · rw [Category.assoc, hGr]
      exact hR
  · rw [← Category.assoc, hGl]
    exact interval_target_of_boundary_diagram L _ _ hLb
  · rw [← Category.assoc, hGr]
    exact hRt

end SerrePositivity.KST.LocalizingInvariants
