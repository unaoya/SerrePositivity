module
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementTriangulated
public import SerrePositivity.DifferentialGraded.Category.TriangleComparison

/-! # 射影的perfect dg加群の実際の標準cone三角形

Hom複体を共有する充満dg部分圏の射を使い、元のmoduleCone・包含・connecting射をH⁰へ運ぶ。
この三角形のdistinguished性は比較のshift整合性を確認した後に証明する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全射影的perfect加群の閉零包含は充満。充満dg部分圏の既存補題を明示する。 -/
instance perfectDGModuleInclusionClosedFull (S : Set D) :
    (perfectDGModuleInclusion A D S).onClosed.Full := by
  dsimp [perfectDGModuleInclusion]
  infer_instance

/-- 全射影的perfect加群の閉零包含は忠実。元の全Homを共有することから従う。 -/
instance perfectDGModuleInclusionClosedFaithful (S : Set D) :
    (perfectDGModuleInclusion A D S).onClosed.Faithful := by
  dsimp [perfectDGModuleInclusion]
  infer_instance

/-- 実際の射影的perfect dg加群のH⁰対象。 -/
def perfectDGModuleHomotopyObj (S : Set D) (M : PerfectDGModuleOver A D S) :
    PerfectDGHomotopyCategoryOver A D S :=
  (toHomotopy A (PerfectDGModuleOver A D S)).obj (ForgetEnrichment.of (Complex A) M)

/-- 全Homを共有する包含の完全忠実性で閉零加群射を持ち上げ、H⁰へ送る。 -/
def perfectDGModuleHomotopyMap (S : Set D) {M N : PerfectDGModuleOver A D S}
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    perfectDGModuleHomotopyObj A D S M ⟶ perfectDGModuleHomotopyObj A D S N :=
  (toHomotopy A (PerfectDGModuleOver A D S)).map
    ((perfectDGModuleInclusion A D S).onClosed.preimage f)

/-- 実際の加群射をH⁰へ持ち上げた後に包含すると、元のK(D)での射に戻る。 -/
lemma perfectDGModuleHomotopyMap_inclusion (S : Set D) {M N : PerfectDGModuleOver A D S}
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    (perfectDGModuleInclusion A D S).onHomotopy.map (perfectDGModuleHomotopyMap A D S f) =
      (moduleToHomotopy A D).map f := by
  change (moduleToHomotopy A D).map
    ((perfectDGModuleInclusion A D S).onClosed.map
      ((perfectDGModuleInclusion A D S).onClosed.preimage f)) = _
  rw [Functor.map_preimage]

/-- 実際の対象の整数shiftは、H⁰の実際のdg shift対象と定義的に一致する。 -/
lemma perfectDGModuleHomotopyObj_shift (S : Set D) (M : PerfectDGModuleOver A D S) (s : ℤ) :
    (perfectDGModuleHomotopyObj A D S M)⟦s⟧ =
      perfectDGModuleHomotopyObj A D S (perfectDGModuleShiftObj A D S s M) := rfl

/-- 実際の標準coneとその包含・connecting射で作るH⁰三角形。微分は+1、connectingの標的はshift 1。 -/
def perfectDGModuleConeTriangle (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    Triangle (PerfectDGHomotopyCategoryOver A D S) :=
  Triangle.mk (perfectDGModuleHomotopyMap A D S f)
    (perfectDGModuleHomotopyMap A D S (M := N) (N := perfectDGModuleCone A D S M N f)
      (moduleConeInr A D f))
    (perfectDGModuleHomotopyMap A D S
      (M := perfectDGModuleCone A D S M N f) (N := perfectDGModuleShiftObj A D S 1 M)
      (moduleConeConnecting A D f) ≫ eqToHom (perfectDGModuleHomotopyObj_shift A D S M 1).symm)

/-- 標準cone三角形の第一射は元の加群射のH⁰像である。 -/
lemma perfectDGModuleConeTriangle_mor₁ (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    (perfectDGModuleConeTriangle A D S M N f).mor₁ = perfectDGModuleHomotopyMap A D S f := rfl

/-- 標準cone三角形の第二射は元のcone包含のH⁰像である。 -/
lemma perfectDGModuleConeTriangle_mor₂ (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    (perfectDGModuleConeTriangle A D S M N f).mor₂ =
      perfectDGModuleHomotopyMap A D S (M := N) (N := perfectDGModuleCone A D S M N f)
        (moduleConeInr A D f) := rfl

/-- 持ち上げたH⁰射は合成を保つ。包含の忠実性で元のK(D)の合成に帰着する。 -/
lemma perfectDGModuleHomotopyMap_comp (S : Set D) {M N P : PerfectDGModuleOver A D S}
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val)
    (g : ForgetEnrichment.of (Complex A) N.val ⟶ ForgetEnrichment.of (Complex A) P.val) :
    perfectDGModuleHomotopyMap A D S (M := M) (N := P) (f ≫ g) =
      perfectDGModuleHomotopyMap A D S f ≫ perfectDGModuleHomotopyMap A D S g := by
  apply (perfectDGModuleInclusion A D S).onHomotopy.map_injective
  rw [Functor.map_comp, perfectDGModuleHomotopyMap_inclusion,
    perfectDGModuleHomotopyMap_inclusion, perfectDGModuleHomotopyMap_inclusion,
    Functor.map_comp]

/-- 持ち上げたH⁰射は恒等射を保つ。 -/
lemma perfectDGModuleHomotopyMap_id (S : Set D) (M : PerfectDGModuleOver A D S) :
    perfectDGModuleHomotopyMap A D S (M := M) (N := M) (𝟙 _) =
      𝟙 (perfectDGModuleHomotopyObj A D S M) := by
  apply (perfectDGModuleInclusion A D S).onHomotopy.map_injective
  exact (perfectDGModuleHomotopyMap_inclusion A D S (𝟙 _)).trans
    (((moduleToHomotopy A D).map_id (ForgetEnrichment.of (Complex A) M.val)).trans
      ((perfectDGModuleInclusion A D S).onHomotopy.map_id
        (perfectDGModuleHomotopyObj A D S M)).symm)

/-- 持ち上げたH⁰射は零射を保つ。 -/
lemma perfectDGModuleHomotopyMap_zero (S : Set D) (M N : PerfectDGModuleOver A D S) :
    perfectDGModuleHomotopyMap A D S (M := M) (N := N) 0 = 0 := by
  apply (perfectDGModuleInclusion A D S).onHomotopy.map_injective
  rw [perfectDGModuleHomotopyMap_inclusion, Functor.map_zero, Functor.map_zero]

/-- 実際の標準cone三角形の最初の二射の合成はH⁰で零となる。 -/
lemma perfectDGModuleConeTriangle_comp_zero₁₂ (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    (perfectDGModuleConeTriangle A D S M N f).mor₁ ≫
      (perfectDGModuleConeTriangle A D S M N f).mor₂ = 0 := by
  apply (perfectDGModuleInclusion A D S).onHomotopy.map_injective
  change (perfectDGModuleInclusion A D S).onHomotopy.map
    (perfectDGModuleHomotopyMap A D S f ≫ perfectDGModuleHomotopyMap A D S
      (M := N) (N := perfectDGModuleCone A D S M N f) (moduleConeInr A D f)) = _
  rw [Functor.map_comp, perfectDGModuleHomotopyMap_inclusion,
    perfectDGModuleHomotopyMap_inclusion, Functor.map_zero]
  exact comp_distTriang_mor_zero₁₂ (moduleHomotopyConeTriangle A D f)
    (moduleHomotopyConeTriangle_distinguished A D f)

/-- 持ち上げたH⁰射の主導来比較は、元の局所化射と標準比較同型で可換である。 -/
lemma perfectDGModuleHomotopyMap_toDerived (S : Set D) {M N : PerfectDGModuleOver A D S}
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    (perfectDGModuleToDerived A D S).map (perfectDGModuleHomotopyMap A D S f) ≫
      (moduleToHomotopyDerivedIso A D).hom.app (ForgetEnrichment.of (Complex A) N.val) =
    (moduleToHomotopyDerivedIso A D).hom.app (ForgetEnrichment.of (Complex A) M.val) ≫
      (moduleToDerived A D).map f := by
  have hc : (perfectDGModuleToDerived A D S).map (perfectDGModuleHomotopyMap A D S f) =
      (moduleToHomotopy A D ⋙ moduleHomotopyToDerivedClosed A D).map f :=
    congrArg (fun g => (moduleHomotopyToDerivedClosed A D).map g)
      (perfectDGModuleHomotopyMap_inclusion A D S f)
  exact (congrArg (fun g => g ≫ (moduleToHomotopyDerivedIso A D).hom.app
    (ForgetEnrichment.of (Complex A) N.val)) hc).trans
      ((moduleToHomotopyDerivedIso A D).hom.naturality f)

/-- 標準cone三角形の第三射は、実際のconnecting射のH⁰像である。 -/
lemma perfectDGModuleConeTriangle_mor₃ (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    (perfectDGModuleConeTriangle A D S M N f).mor₃ =
      perfectDGModuleHomotopyMap A D S
        (M := perfectDGModuleCone A D S M N f) (N := perfectDGModuleShiftObj A D S 1 M)
        (moduleConeConnecting A D f) :=
  Category.comp_id _

/-- 任意のshift整合関手で写した標準cone三角形の第三射を、実際のconnecting射で評価する。 -/
lemma perfectDGModuleConeTriangle_map_mor₃ (S : Set D) {E : Type w} [Category.{w'} E]
    [HasShift E ℤ] (F : PerfectDGHomotopyCategoryOver A D S ⥤ E) [F.CommShift ℤ]
    (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    (F.mapTriangle.obj (perfectDGModuleConeTriangle A D S M N f)).mor₃ =
      F.map (perfectDGModuleHomotopyMap A D S
        (M := perfectDGModuleCone A D S M N f) (N := perfectDGModuleShiftObj A D S 1 M)
        (moduleConeConnecting A D f)) ≫
      (F.commShiftIso (1 : ℤ)).hom.app (perfectDGModuleHomotopyObj A D S M) :=
  triangleComparison_mor₃ F (perfectDGModuleConeTriangle A D S M N f)
    (perfectDGModuleHomotopyMap A D S
      (M := perfectDGModuleCone A D S M N f) (N := perfectDGModuleShiftObj A D S 1 M)
      (moduleConeConnecting A D f)) (perfectDGModuleConeTriangle_mor₃ A D S M N f)

end SerrePositivity.DifferentialGraded
