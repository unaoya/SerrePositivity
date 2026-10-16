module
public import SerrePositivity.DifferentialGraded.Category.FullSubcategory
public import SerrePositivity.DifferentialGraded.Perfect.Triangulated
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveResolution
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveLocalizationHom

/-! # 射影的perfect dg加群による主Perfのenhancement

対象は実際の右dg加群、Homは元の全次数Hom endである。
小さい代表系への制限は別に証明し、この対象型全体をsmallと仮定しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 実際の右dg加群が射影的で、その主導来像が指定生成集合SのPerfに入るという性質。 -/
def modulePerfectProjectiveOver (S : Set D) (M : RightModule A D) : Prop :=
  moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) M) ∧
    modulePerfectOver A D S ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) M))

/-- 射影的perfect右dg加群の充満dg部分圏。全対象のsmall性は仮定しない。 -/
abbrev PerfectDGModuleOver (S : Set D) :=
  DGFullSubcategory (RightModule A D) (modulePerfectProjectiveOver A D S)

/-- 全代表加群から生成する射影的perfect dg部分圏。 -/
abbrev PerfectDGModule := PerfectDGModuleOver A D Set.univ

/-- 射影的perfect加群から全右dg加群への全Homを保つ包含。 -/
def perfectDGModuleInclusion (S : Set D) :
    DGFunctor A (PerfectDGModuleOver A D S) (RightModule A D) :=
  dgFullSubcategoryInclusion A (RightModule A D) (modulePerfectProjectiveOver A D S)

/-- 射影的perfect加群のH⁰包含は充満。充満dg部分圏の一般補題を適用する。 -/
instance perfectDGModuleInclusionHomotopyFull (S : Set D) :
    (perfectDGModuleInclusion A D S).onHomotopy.Full := by
  dsimp [perfectDGModuleInclusion]
  infer_instance

/-- 射影的perfect加群のH⁰包含は忠実。同一のHomと境界関係を使う。 -/
instance perfectDGModuleInclusionHomotopyFaithful (S : Set D) :
    (perfectDGModuleInclusion A D S).onHomotopy.Faithful := by
  dsimp [perfectDGModuleInclusion]
  infer_instance

/-- 射影的perfect dg部分圏の実際のH⁰。 -/
abbrev PerfectDGHomotopyCategoryOver (S : Set D) := HomotopyCategory A (PerfectDGModuleOver A D S)

/-- H⁰包含を既存K(D)から主導来圏への関手と合成した比較。 -/
def perfectDGModuleToDerived (S : Set D) :
    PerfectDGHomotopyCategoryOver A D S ⥤ DerivedModuleCategory A D :=
  (perfectDGModuleInclusion A D S).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D

/-- 比較の像は指定Perfに入る。Qとの自然同型で対象に保持した証拠を運ぶ。 -/
lemma perfectDGModuleToDerived_obj_perfect (S : Set D) (X : PerfectDGHomotopyCategoryOver A D S) :
    modulePerfectOver A D S ((perfectDGModuleToDerived A D S).obj X) := by
  let M : PerfectDGModuleOver A D S := ForgetEnrichment.to (Complex A) X.as
  exact (modulePerfectOver A D S).prop_of_iso
    ((moduleToHomotopyDerivedIso A D).app (ForgetEnrichment.of (Complex A) M.val)).symm M.property.2

/-- 主導来比較は充満。始域の射影性による局所化Hom計算とH⁰包含の充満性を使う。 -/
instance perfectDGModuleToDerivedFull (S : Set D) : (perfectDGModuleToDerived A D S).Full where
  map_surjective {X Y} f := by
    let M : PerfectDGModuleOver A D S := ForgetEnrichment.to (Complex A) X.as
    let N : ModuleCategory A D := ForgetEnrichment.of (Complex A) M.val
    obtain ⟨g, hg⟩ := (moduleProjectiveLocalization_map_bijective A D
      (P := N) M.property.1 ((perfectDGModuleInclusion A D S).onHomotopy.obj Y)).2 f
    obtain ⟨h, hh⟩ := (perfectDGModuleInclusion A D S).onHomotopy.map_surjective g
    refine ⟨h, ?_⟩
    change (moduleHomotopyToDerivedClosed A D).map
      ((perfectDGModuleInclusion A D S).onHomotopy.map h) = f
    rw [hh]
    exact hg

/-- 主導来比較は忠実。射影対象からの局所化Hom写像の単射性を使う。 -/
instance perfectDGModuleToDerivedFaithful (S : Set D) :
    (perfectDGModuleToDerived A D S).Faithful where
  map_injective {X Y} f g h := by
    let M : PerfectDGModuleOver A D S := ForgetEnrichment.to (Complex A) X.as
    let N : ModuleCategory A D := ForgetEnrichment.of (Complex A) M.val
    apply (perfectDGModuleInclusion A D S).onHomotopy.map_injective
    exact (moduleProjectiveLocalization_map_bijective A D
      (P := N) M.property.1 ((perfectDGModuleInclusion A D S).onHomotopy.obj Y)).1 h

/-- 主導来比較を、その全本質像を含む指定Perfへ制限する。 -/
def perfectDGModuleToPerfect (S : Set D) :
    PerfectDGHomotopyCategoryOver A D S ⥤ PerfectModuleCategoryOver A D S :=
  (modulePerfectOver A D S).lift (perfectDGModuleToDerived A D S)
    (perfectDGModuleToDerived_obj_perfect A D S)

/-- Perfへの制限も充満。充満部分圏への持ち上げの性質を用いる。 -/
instance perfectDGModuleToPerfectFull (S : Set D) : (perfectDGModuleToPerfect A D S).Full := by
  dsimp [perfectDGModuleToPerfect]
  infer_instance

/-- Perfへの制限も忠実。主導来比較の忠実性を継承する。 -/
instance perfectDGModuleToPerfectFaithful (S : Set D) :
    (perfectDGModuleToPerfect A D S).Faithful := by
  dsimp [perfectDGModuleToPerfect]
  infer_instance

/-- 任意のPerf対象を標準射影解像度で表し、本質的全射性を得る。smallな代表選択は別工程である。 -/
instance perfectDGModuleToPerfectEssSurj (S : Set D) :
    (perfectDGModuleToPerfect A D S).EssSurj where
  mem_essImage X := by
    let R := moduleCanonicalProjectiveResolution A D X.obj.as.obj
    let e : (moduleToDerived A D).obj R.obj ≅ X.obj := moduleDerivedIso A D R.π R.quasiIso
    let M : PerfectDGModuleOver A D S :=
      ⟨ForgetEnrichment.to (Complex A) R.obj, R.projective,
        (modulePerfectOver A D S).prop_of_iso e.symm X.property⟩
    refine ⟨(toHomotopy A (PerfectDGModuleOver A D S)).obj
      (ForgetEnrichment.of (Complex A) M), ⟨(modulePerfectOver A D S).isoMk ?_⟩⟩
    exact (moduleToHomotopyDerivedIso A D).app R.obj ≪≫ e

/-- 完全忠実性と射影解像度による本質的全射性から比較は同値となる。 -/
instance perfectDGModuleToPerfectIsEquivalence (S : Set D) :
    (perfectDGModuleToPerfect A D S).IsEquivalence where

/-- 射影的perfect加群のH⁰と主Perfの同値。shift・三角構造の比較は別に検証する。 -/
def perfectDGModuleHomotopyEquivalence (S : Set D) :
    PerfectDGHomotopyCategoryOver A D S ≌ PerfectModuleCategoryOver A D S :=
  (perfectDGModuleToPerfect A D S).asEquivalence

end SerrePositivity.DifferentialGraded
