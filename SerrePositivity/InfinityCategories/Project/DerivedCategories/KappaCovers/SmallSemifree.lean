module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.GradedExtension
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSphereFreeCover
public import SerrePositivity.DifferentialGraded.Perfect.Compact.FiniteGeneration
public import SerrePositivity.DifferentialGraded.Derived.Basic

/-!
概要：各自由層が κ-small な実 semifree 加群を、同じ選択代表系で K(D) 同型まで被覆する。
方針：小さい sphere 層、全次数分裂する拡大、可算 telescope と実余極限の準同型を順に使う。
規約：任意の semifree がこの濃度条件を満たすとは主張しない。
使われ方：D-8 d の κ-small cell 部分表示の各段の代表化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory Limits Pretriangulated DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
include hκ hreg

lemma dgKappaCoversImage_smallSphereFree {M : ModuleCategory R D}
    (p : ModuleSphereFreePresentation R D M) (hp : HasCardinalLT p.Index κ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCoversImage R D κ ((moduleToHomotopy R D).obj M) := by
  letI := p.smallIndex
  let e := equivShrink p.Index
  have hs : HasCardinalLT (Shrink.{u} p.Index) κ := (hasCardinalLT_iff_of_equiv e κ).mp hp
  obtain ⟨i, ⟨ei⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule_covers R D (Shrink.{u} p.Index)
    (fun a => p.object (e.symm a)) (fun a => p.degree (e.symm a))
    ((hasCardinalLT_iff_cardinal_mk_lt _ _).mp hs)
  have ep : M ≅ ∐ (fun a : Shrink.{u} p.Index => freeSphere R D (p.object (e.symm a))
      (p.degree (e.symm a))) := p.iso ≪≫ Sigma.whiskerEquiv e (fun a => by
        simp only [Equiv.symm_apply_apply]
        exact Iso.refl _)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCoversImage_iff R D κ _).mpr
    ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R D i, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_sphereFree R D hκ i,
      ⟨(moduleToHomotopy R D).mapIso (ei ≪≫ ep.symm)⟩⟩

lemma dgKappaCoversImage_sequential_projective (F : ℕ ⥤ ModuleCategory R D)
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ n, moduleHomotopicallyProjective R D (F.obj n))
    (hC : moduleHomotopicallyProjective R D c.pt)
    (hFI : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCoversImage R D κ ((moduleToHomotopy R D).obj (F.obj n))) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCoversImage R D κ ((moduleToHomotopy R D).obj c.pt) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCoversImage_isTriangulated R D κ hκ hreg
  let B := sequentialCoproductFamily.{u} F
  have hBI : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCoversImage R D κ ((moduleToHomotopy R D).obj (∐ B)) := by
    have he0 : (moduleToHomotopy R D).obj (∐ B) ≅
        ∐ (fun n : ULift.{u} ℕ => (moduleToHomotopy R D).obj (F.obj n.down)) := by
      exact (moduleHomotopyCofanIsColimit R D B).coconePointUniqueUpToIso
        (coproductIsCoproduct (fun n => (moduleToHomotopy R D).obj (B n)))
    have he1 : (∐ fun n : ULift.{u} ℕ => (moduleToHomotopy R D).obj (F.obj n.down)) ≅
        ∐ (fun n : ℕ => (moduleToHomotopy R D).obj (F.obj n)) :=
      Sigma.whiskerEquiv (Equiv.ulift : ULift.{u} ℕ ≃ ℕ)
        (fun n => Iso.refl ((moduleToHomotopy R D).obj (F.obj n.down)))
    let he := he0 ≪≫ he1
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCoversImage R D κ).prop_of_iso he.symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCoversImage_countable R D hκ hreg _ hFI)
  let f := sequentialCoproductMap.{u} F
  have hcone : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCoversImage R D κ ((moduleToHomotopy R D).obj (moduleCone R D f)) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCoversImage R D κ).ext_of_isTriangulatedClosed₃
      (moduleHomotopyConeTriangle R D f) (moduleHomotopyConeTriangle_distinguished R D f) hBI hBI
  have hB := moduleCoproduct_homotopicallyProjective R D B (fun n => hF n.down)
  let q := moduleSequentialConeDesc R D F c
  have hi := moduleHomotopicallyProjective_quasiIso_isIso_homotopy R D
    (moduleHomotopicallyProjective_cone R D hB hB f) hC q
    (moduleSequentialConeDesc_quasiIso R D F c hc)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCoversImage R D κ).prop_of_iso (asIso ((moduleToHomotopy R D).map q)) hcone

/-- 小さい実 semifree の各層を同じ代表族へ戻す。 -/
lemma dgKappaCoversImage_smallSemifree {M : ModuleCategory R D}
    (F : ModuleSemifreeFiltration R D M)
    (h0 : HasCardinalLT F.initial.Index κ)
    (hQ : ∀ n, HasCardinalLT (F.quotientPresentation n).Index κ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCoversImage R D κ ((moduleToHomotopy R D).obj M) := by
  have hstage : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCoversImage R D κ ((moduleToHomotopy R D).obj (F.stage n)) := by
    intro n
    induction n with
    | zero => exact dgKappaCoversImage_smallSphereFree R D hκ hreg F.initial h0
    | succ n ih =>
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCoversImage_gradedExtension R D hκ hreg (F.split n)
        (F.stage_homotopicallyProjective R D n) (F.quotient_homotopicallyProjective R D n) ih
        (dgKappaCoversImage_smallSphereFree R D hκ hreg (F.quotientPresentation n) (hQ n))
  have hC := dgKappaCoversImage_sequential_projective R D hκ hreg
    (Functor.ofSequence F.transition) F.cocone F.isColimit
    (F.stage_homotopicallyProjective R D)
    (moduleHomotopicallyProjective_of_iso R D F.iso.symm (F.homotopicallyProjective R D)) hstage
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCoversImage R D κ).prop_of_iso ((moduleToHomotopy R D).mapIso F.iso) hC

lemma dgKappaClosedProjectiveObjects_smallSemifreeCovers {M : ModuleCategory R D}
    (F : ModuleSemifreeFiltration R D M)
    (h0 : HasCardinalLT F.initial.Index κ)
    (hQ : ∀ n, HasCardinalLT (F.quotientPresentation n).Index κ) :
    ∃ N : ModuleCategory R D, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ N ∧
      Nonempty ((moduleToHomotopy R D).obj N ≅ (moduleToHomotopy R D).obj M) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCoversImage_iff R D κ _).mp (dgKappaCoversImage_smallSemifree R D hκ hreg F h0 hQ)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
