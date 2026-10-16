module
public import SerrePositivity.DifferentialGraded.Category.Restriction
public import SerrePositivity.DifferentialGraded.Perfect.Enhancement
public import SerrePositivity.DifferentialGraded.Perfect.UniversalProperty

/-! # 射影的perfect dg圏における実際の有限操作

主dg加群のshift・和・coneをそのまま使い、射影性と主導来像のperfect性を確認する。
小さい代表系での操作は、これらの対象を選択した代表へ戻すことで後に比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 零加群は射影的perfect。零の有限cell構成から両条件を得る。 -/
lemma modulePerfectProjectiveOver_zero (S : Set D) :
    modulePerfectProjectiveOver A D S (ForgetEnrichment.to (Complex A) (moduleZero A D)) :=
  ⟨moduleFiniteCellOver_homotopicallyProjective A D (moduleFiniteCellOver_zero A D S),
    modulePerfectOver_of_finiteCell A D (moduleFiniteCellOver_zero A D S)⟩

/-- 射影的perfect加群の実際のdg shiftは再び射影的perfect。主局所化のshift比較を使用する。 -/
lemma modulePerfectProjectiveOver_shift {S : Set D} {M : RightModule A D}
    (hM : modulePerfectProjectiveOver A D S M) (s : ℤ) :
    modulePerfectProjectiveOver A D S (shiftModule s M) := by
  let X : ModuleCategory A D := ForgetEnrichment.of (Complex A) M
  exact ⟨moduleHomotopicallyProjective_shift A D hM.1 s,
    (modulePerfectOver A D S).prop_of_iso (((moduleToDerived A D).commShiftIso s).app X).symm
      (modulePerfectOver_shift A D hM.2 s)⟩

/-- 射影的perfect加群間の任意の閉零射の標準coneは射影的perfect。三角閉性を主導来像に適用する。 -/
lemma modulePerfectProjectiveOver_cone {S : Set D} {M N : ModuleCategory A D}
    (hM : modulePerfectProjectiveOver A D S (ForgetEnrichment.to (Complex A) M))
    (hN : modulePerfectProjectiveOver A D S (ForgetEnrichment.to (Complex A) N)) (f : M ⟶ N) :
    modulePerfectProjectiveOver A D S (ForgetEnrichment.to (Complex A) (moduleCone A D f)) := by
  refine ⟨moduleHomotopicallyProjective_cone A D hM.1 hN.1 f, ?_⟩
  have h := (modulePerfectOver A D S).ext_of_isTriangulatedClosed₃'
    (moduleDerivedConeTriangle A D f)
    (moduleDerivedConeTriangle_distinguished A D f) hM.2 hN.2
  rw [ObjectProperty.isoClosure_eq_self] at h
  exact h

/-- 射影的perfect加群の実際の二項和も射影的perfect。主導来関手の和比較を通じて運ぶ。 -/
lemma modulePerfectProjectiveOver_biprod {S : Set D} {M N : ModuleCategory A D}
    (hM : modulePerfectProjectiveOver A D S (ForgetEnrichment.to (Complex A) M))
    (hN : modulePerfectProjectiveOver A D S (ForgetEnrichment.to (Complex A) N)) :
    modulePerfectProjectiveOver A D S (ForgetEnrichment.to (Complex A) (moduleBiprod A D M N)) :=
  ⟨moduleHomotopicallyProjective_biprod A D hM.1 hN.1,
    moduleDerivedBiprod_mem_triangulated A D (modulePerfectOver A D S) hM.2 hN.2⟩

/-- 全射影的perfect dg圏の実際の零加群。 -/
def perfectDGModuleZero (S : Set D) : PerfectDGModuleOver A D S :=
  ⟨ForgetEnrichment.to (Complex A) (moduleZero A D), modulePerfectProjectiveOver_zero A D S⟩

/-- 全射影的perfect dg圏の実際の整数shift対象。 -/
def perfectDGModuleShiftObj (S : Set D) (s : ℤ) (M : PerfectDGModuleOver A D S) :
    PerfectDGModuleOver A D S :=
  ⟨shiftModule s M.val, modulePerfectProjectiveOver_shift A D M.property s⟩

/-- 既存の全Hom shiftを制限した真のdg自己関手。単位と合成は既存加群shiftから継承する。 -/
def perfectDGModuleShiftDG (S : Set D) (s : ℤ) :
    DGFunctor A (PerfectDGModuleOver A D S) (PerfectDGModuleOver A D S) :=
  (moduleShiftDG A D s).restrict (modulePerfectProjectiveOver A D S)
    (modulePerfectProjectiveOver A D S) (fun _ h => modulePerfectProjectiveOver_shift A D h s)

/-- dg shiftと全加群への包含は、全Homの射を含めて同じdg関手を与える。 -/
lemma perfectDGModuleShiftDG_comp_inclusion (S : Set D) (s : ℤ) :
    DGFunctor.comp (perfectDGModuleShiftDG A D S s) (perfectDGModuleInclusion A D S) =
      DGFunctor.comp (perfectDGModuleInclusion A D S) (moduleShiftDG A D s) :=
  (moduleShiftDG A D s).restrict_comp_inclusion (modulePerfectProjectiveOver A D S)
    (modulePerfectProjectiveOver A D S) (fun _ h => modulePerfectProjectiveOver_shift A D h s)


/-- 二つの射影的perfect加群の実際の二項和。 -/
def perfectDGModuleBiprod (S : Set D) (M N : PerfectDGModuleOver A D S) :
    PerfectDGModuleOver A D S :=
  ⟨ForgetEnrichment.to (Complex A) (moduleBiprod A D
      (ForgetEnrichment.of (Complex A) M.val) (ForgetEnrichment.of (Complex A) N.val)),
    modulePerfectProjectiveOver_biprod A D M.property N.property⟩

/-- 射影的perfect加群間の閉零射に対する実際の標準cone対象。 -/
def perfectDGModuleCone (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    PerfectDGModuleOver A D S :=
  ⟨ForgetEnrichment.to (Complex A) (moduleCone A D f),
    modulePerfectProjectiveOver_cone A D M.property N.property f⟩

/-- 閉零代表から主導来圏への比較は、元の局所化Qと自然同型で一致する。 -/
def perfectDGModuleClosedToDerivedIso (S : Set D) :
    toHomotopy A (PerfectDGModuleOver A D S) ⋙ perfectDGModuleToDerived A D S ≅
      (perfectDGModuleInclusion A D S).onClosed ⋙ moduleToDerived A D :=
  NatIso.ofComponents
    (fun M => (moduleToHomotopyDerivedIso A D).app
      ((perfectDGModuleInclusion A D S).onClosed.obj M))
    (fun f => (moduleToHomotopyDerivedIso A D).hom.naturality
      ((perfectDGModuleInclusion A D S).onClosed.map f))

/-- 実際のdg shift対象の主導来像は、比較像の整数shiftと同型である。 -/
def perfectDGModuleShiftDerivedIso (S : Set D) (s : ℤ) (M : PerfectDGModuleOver A D S) :
    (perfectDGModuleToDerived A D S).obj
      ((toHomotopy A (PerfectDGModuleOver A D S)).obj
        (ForgetEnrichment.of (Complex A) (perfectDGModuleShiftObj A D S s M))) ≅
    ((perfectDGModuleToDerived A D S).obj
      ((toHomotopy A (PerfectDGModuleOver A D S)).obj
        (ForgetEnrichment.of (Complex A) M)))⟦s⟧ :=
  (moduleToHomotopyDerivedIso A D).app
      ((ForgetEnrichment.of (Complex A) M.val)⟦s⟧) ≪≫
    ((moduleToDerived A D).commShiftIso s).app (ForgetEnrichment.of (Complex A) M.val) ≪≫
    (shiftFunctor (DerivedModuleCategory A D) s).mapIso
      ((moduleToHomotopyDerivedIso A D).app (ForgetEnrichment.of (Complex A) M.val)).symm

end SerrePositivity.DifferentialGraded
