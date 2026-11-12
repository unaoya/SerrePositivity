module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedColimit

/-!
概要：指定次数の斉次局所化の filtered 図式と、余極限の分子族の局所化を比較する。
方針：分母を固定した分数の分子を有限段へ降ろす。
規約：多項式作用の環 P と分子族の基底 R を分け、分母に非零因子性を仮定しない。
使われ方：動く基底の実際の標準開の Čech 図式への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R P : Type u} [CommRing R] [CommRing P] [Algebra R P]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (M : J ⥤ ModuleCat.{u} P)
local instance gradedAwayColimitStageBaseModule (j : J) : Module R (M.obj j) :=
  Module.compHom (M.obj j) (algebraMap R P)
local instance gradedAwayColimitStageBaseTower (j : J) : IsScalarTower R P (M.obj j) :=
  IsScalarTower.of_compHom R P (M.obj j)
local instance gradedAwayColimitTargetBaseModule : Module R (colimit M : ModuleCat.{u} P) :=
  Module.compHom (colimit M : ModuleCat.{u} P) (algebraMap R P)
local instance gradedAwayColimitTargetBaseTower :
    IsScalarTower R P (colimit M : ModuleCat.{u} P) :=
  IsScalarTower.of_compHom R P (colimit M : ModuleCat.{u} P)


variable (G : ∀ j, ℕ → Submodule R (M.obj j))
variable (hG : ∀ {i j} (α : i ⟶ j) (n : ℕ) (m : M.obj i),
  m ∈ G i n → (M.map α).hom m ∈ G j n)
variable (f : P)

/-- 各有限段の指定次数の斉次局所化からなる filtered 図式。 -/
def projectiveGradedAwayColimitDiagram : J ⥤ ModuleCat.{u} R where
  obj j := ModuleCat.of R (projectiveGradedAway f (G j))
  map {i j} α := ModuleCat.ofHom
    (projectiveGradedAwayMap f (G i) (G j) (M.map α).hom (hG α))
  map_id j := by
    apply ModuleCat.hom_ext
    simpa only [M.map_id, ModuleCat.hom_id, ModuleCat.hom_ofHom] using
      projectiveGradedAwayMap_id f (G j)
  map_comp {i j k} α β := by
    apply ModuleCat.hom_ext
    simpa only [M.map_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
      projectiveGradedAwayMap_comp f (G i) (G j) (G k)
        (M.map α).hom (M.map β).hom (hG α) (hG β)

/-- 有限段の斉次局所化から、余極限の分子族の斉次局所化への canonical な余錐。 -/
def projectiveGradedAwayColimitCocone : Cocone (projectiveGradedAwayColimitDiagram M G hG f) where
  pt := ModuleCat.of R (projectiveGradedAway f (projectiveGradedColimitGrade M G))
  ι :=
    { app j := ModuleCat.ofHom
        (projectiveGradedAwayMap f (G j) (projectiveGradedColimitGrade M G)
          (colimit.ι M j).hom (projectiveGradedColimitInclusion_preservesPiece M G hG j))
      naturality {i j} α := by
        simp only [Functor.const_obj_map]
        apply ModuleCat.hom_ext
        simp only [projectiveGradedAwayColimitDiagram, ModuleCat.hom_comp,
          ModuleCat.hom_ofHom, ModuleCat.hom_id, LinearMap.id_comp]
        rw [← projectiveGradedAwayMap_comp]
        congr 1
        exact congrArg ModuleCat.Hom.hom (colimit.w M α) }

/-- 指定次数の局所化の colimit から、実際の余極限の分子族の局所化への比較射。 -/
def projectiveGradedAwayColimitMap :
    colimit (projectiveGradedAwayColimitDiagram M G hG f) ⟶
      ModuleCat.of R (projectiveGradedAway f (projectiveGradedColimitGrade M G)) :=
  colimit.desc _ (projectiveGradedAwayColimitCocone M G hG f)

/-- 比較射は、各有限段の分数をその段の射で移す。 -/
theorem projectiveGradedAwayColimitMap_ι (j : J) (z : projectiveGradedAway f (G j)) :
    (projectiveGradedAwayColimitMap M G hG f).hom
        ((colimit.ι (projectiveGradedAwayColimitDiagram M G hG f) j).hom z) =
      projectiveGradedAwayMap f (G j) (projectiveGradedColimitGrade M G)
        (colimit.ι M j).hom (projectiveGradedColimitInclusion_preservesPiece M G hG j) z :=
  congrArg (fun α ↦ α.hom z) (colimit.ι_desc (projectiveGradedAwayColimitCocone M G hG f) j)

variable (hstep : ∀ j n (m : G j n), f • m.val ∈ G j (n + 1))

include hstep

/-- 各段の分母倍の条件の下で、斉次局所化の filtered colimit の比較は全射。 -/
theorem projectiveGradedAwayColimitMap_surjective :
    Function.Surjective (projectiveGradedAwayColimitMap M G hG f).hom := by
  intro z
  obtain ⟨n, m, hm⟩ := (mem_projectiveGradedAway_iff f (projectiveGradedColimitGrade M G)
    (projectiveGradedColimitGrade_step M G hG f hstep) z.val).mp z.property
  obtain ⟨j, a, ha, he⟩ := (mem_projectiveGradedColimitGrade_iff M G hG n m.val).mp m.property
  let b : projectiveGradedAway f (G j) :=
    ⟨projectiveGradedFraction f (G j) n ⟨a, ha⟩,
      (le_iSup (fun k ↦ LinearMap.range (projectiveGradedFraction f (G j) k)) n)
        (LinearMap.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩)⟩
  refine ⟨(colimit.ι (projectiveGradedAwayColimitDiagram M G hG f) j).hom b, ?_⟩
  apply Subtype.ext
  have hι := congrArg Subtype.val (projectiveGradedAwayColimitMap_ι M G hG f j b)
  have hfrac := projectiveGradedAwayMap_fraction f (G j) (projectiveGradedColimitGrade M G)
    (colimit.ι M j).hom (projectiveGradedColimitInclusion_preservesPiece M G hG j)
    n ⟨a, ha⟩ b rfl
  refine hι.trans (hfrac.trans ?_)
  simpa only [projectiveGradedFraction_apply, he] using hm

/-- 分母倍での零化を有限段へ降ろすことで、斉次局所化の比較は単射となる。 -/
theorem projectiveGradedAwayColimitMap_injective :
    Function.Injective (projectiveGradedAwayColimitMap M G hG f).hom := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  obtain ⟨j, b, rfl⟩ := Concrete.colimit_exists_rep
    (projectiveGradedAwayColimitDiagram M G hG f) z
  have hzval : (projectiveGradedAwayMap f (G j) (projectiveGradedColimitGrade M G)
      (colimit.ι M j).hom (projectiveGradedColimitInclusion_preservesPiece M G hG j) b).val = 0 := by
    change (projectiveGradedAwayColimitMap M G hG f).hom
      ((colimit.ι (projectiveGradedAwayColimitDiagram M G hG f) j).hom b) = 0 at hz
    rw [projectiveGradedAwayColimitMap_ι] at hz
    exact congrArg Subtype.val hz
  obtain ⟨n, m, hm⟩ := (mem_projectiveGradedAway_iff f (G j) (hstep j) b.val).mp b.property
  have hf : LocalizedModule.mk ((colimit.ι M j).hom m.val) (projDenominator f n) = 0 := by
    have hfrac := projectiveGradedAwayMap_fraction f (G j) (projectiveGradedColimitGrade M G)
      (colimit.ι M j).hom (projectiveGradedColimitInclusion_preservesPiece M G hG j) n m b hm
    simpa only [projectiveGradedFraction_apply] using hfrac.symm.trans hzval
  obtain ⟨t, ht⟩ := LocalizedModule.mk_eq.mp
    (hf.trans (LocalizedModule.zero_mk (1 : Submonoid.powers f)).symm)
  have ht' : t.val • (colimit.ι M j).hom m.val = 0 := by
    simpa only [Submonoid.smul_def, one_smul, smul_zero] using ht
  have he : (colimit.ι M j).hom (t.val • m.val) = (colimit.ι M j).hom 0 := by
    simpa only [map_smul, map_zero] using ht'
  obtain ⟨k, α, hα⟩ := (colimit.isColimit M).eq_iff' (t.val • m.val) 0 |>.mp he
  have htα : t.val • (M.map α).hom m.val = 0 := by
    simpa only [map_smul, map_zero] using hα
  have hb : ((projectiveGradedAwayColimitDiagram M G hG f).map α).hom b = 0 := by
    apply Subtype.ext
    change (projectiveGradedAwayMap f (G j) (G k) (M.map α).hom (hG α) b).val = 0
    rw [projectiveGradedAwayMap_fraction f (G j) (G k) (M.map α).hom (hG α) n m b hm,
      projectiveGradedFraction_apply, ← LocalizedModule.zero_mk (1 : Submonoid.powers f)]
    apply LocalizedModule.mk_eq.mpr
    exact ⟨t, by simpa only [Submonoid.smul_def, one_smul, smul_zero] using htα⟩
  have hw := congrArg (fun α ↦ α.hom b)
    (colimit.w (projectiveGradedAwayColimitDiagram M G hG f) α)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hb, map_zero] at hw
  exact hw.symm

/-- 実際の斉次局所化の filtered colimit と、余極限の分子族の斉次局所化との同型。 -/
def projectiveGradedAwayColimitEquiv :
    (colimit (projectiveGradedAwayColimitDiagram M G hG f) : ModuleCat.{u} R) ≃ₗ[R]
      projectiveGradedAway f (projectiveGradedColimitGrade M G) :=
  LinearEquiv.ofBijective (projectiveGradedAwayColimitMap M G hG f).hom
    ⟨projectiveGradedAwayColimitMap_injective M G hG f hstep,
      projectiveGradedAwayColimitMap_surjective M G hG f hstep⟩

/-- 斉次局所化の同型は、各有限段からの実際の分数の写像を保つ。 -/
theorem projectiveGradedAwayColimitEquiv_ι (j : J) (z : projectiveGradedAway f (G j)) :
    projectiveGradedAwayColimitEquiv M G hG f hstep
        ((colimit.ι (projectiveGradedAwayColimitDiagram M G hG f) j).hom z) =
      projectiveGradedAwayMap f (G j) (projectiveGradedColimitGrade M G)
        (colimit.ι M j).hom (projectiveGradedColimitInclusion_preservesPiece M G hG j) z :=
  projectiveGradedAwayColimitMap_ι M G hG f j z

end SerrePositivity.AlgebraicGeometry
