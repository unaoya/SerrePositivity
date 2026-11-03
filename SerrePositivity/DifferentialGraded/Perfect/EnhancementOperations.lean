module

public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement
public import SerrePositivity.DifferentialGraded.Perfect.Basic

public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import Mathlib.CategoryTheory.Shift.Induced
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.CategoryTheory.Triangulated.Adjunction



/-!
# Perfect.EnhancementOperations

## 概要
8 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## EnhancementOperations（旧 SerrePositivity/DifferentialGraded/Perfect/EnhancementOperations.lean） -/

/-! # 射影的perfect dg圏における実際の有限操作

主dg加群のshift・和・coneをそのまま使い、射影性と主導来像のperfect性を確認する。
小さい代表系での操作は、これらの対象を選択した代表へ戻すことで後に比較する。
-/

@[expose] public section EnhancementOperations
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end EnhancementOperations

/-! ## EnhancementShiftComparison（旧 SerrePositivity/DifferentialGraded/Perfect/EnhancementShiftComparison.lean） -/

/-! # 射影的perfect dg shiftのH⁰と主Perfにおける自然比較 -/

@[expose] public section EnhancementShiftComparison
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 実際のdg shiftのH⁰は、H⁰包含の後の既存K(D)のshiftと自然に可換である。 -/
def perfectDGModuleShiftHomotopyInclusionIso (S : Set D) (s : ℤ) :
    (perfectDGModuleShiftDG A D S s).onHomotopy ⋙ (perfectDGModuleInclusion A D S).onHomotopy ≅
      (perfectDGModuleInclusion A D S).onHomotopy ⋙ shiftFunctor (ModuleHomotopyCategory A D) s :=
  restrictHomotopyComparisonIso (moduleShiftDG A D s) (modulePerfectProjectiveOver A D S)
    (fun _ h => modulePerfectProjectiveOver_shift A D h s)
    (shiftFunctor (ModuleHomotopyCategory A D) s) (moduleShiftDGHomotopyIso A D s)


/-- 実際のdg shiftのH⁰比較は全てのH⁰射について主導来shiftと自然に可換である。 -/
def perfectDGModuleShiftHomotopyDerivedIso (S : Set D) (s : ℤ) :
    (perfectDGModuleShiftDG A D S s).onHomotopy ⋙ perfectDGModuleToDerived A D S ≅
      perfectDGModuleToDerived A D S ⋙ shiftFunctor (DerivedModuleCategory A D) s :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (perfectDGModuleShiftHomotopyInclusionIso A D S s)
      (moduleHomotopyToDerivedClosed A D) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (perfectDGModuleInclusion A D S).onHomotopy
      ((moduleHomotopyToDerivedClosed A D).commShiftIso s) ≪≫
    (Functor.associator _ _ _).symm

/-- 主導来shiftとの自然比較を、既存の充満部分圏としてのPerfへ持ち上げる。 -/
def perfectDGModuleShiftHomotopyPerfectIso (S : Set D) (s : ℤ) :
    (perfectDGModuleShiftDG A D S s).onHomotopy ⋙ perfectDGModuleToPerfect A D S ≅
      perfectDGModuleToPerfect A D S ⋙ shiftFunctor (PerfectModuleCategoryOver A D S) s := by
  let I := (modulePerfectOver A D S).ι
  let e := perfectDGModuleToPerfectCompInclusion A D S
  exact ((Functor.FullyFaithful.ofFullyFaithful I).whiskeringRight
    (PerfectDGHomotopyCategoryOver A D S)).preimageIso
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ e ≪≫ perfectDGModuleShiftHomotopyDerivedIso A D S s ≪≫
        Functor.isoWhiskerRight e.symm (shiftFunctor (DerivedModuleCategory A D) s) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (perfectDGModuleToPerfect A D S) (I.commShiftIso s).symm ≪≫
        (Functor.associator _ _ _).symm)

/-- 主Perfのshift比較を包含で写すと、主導来比較と包含のshift比較の逆の合成になる。 -/
lemma perfectDGModuleShiftHomotopyPerfectIso_hom_inclusion (S : Set D) (s : ℤ)
    (X : PerfectDGHomotopyCategoryOver A D S) :
    (modulePerfectOver A D S).ι.map
      ((perfectDGModuleShiftHomotopyPerfectIso A D S s).hom.app X) =
    (perfectDGModuleShiftHomotopyDerivedIso A D S s).hom.app X ≫
      ((modulePerfectOver A D S).ι.commShiftIso s).inv.app
        ((perfectDGModuleToPerfect A D S).obj X) := by
  suffices h : ((Functor.FullyFaithful.ofFullyFaithful (modulePerfectOver A D S).ι).preimage
      (X := (perfectDGModuleToPerfect A D S).obj
        ((perfectDGModuleShiftDG A D S s).onHomotopy.obj X))
      (Y := ((perfectDGModuleToPerfect A D S).obj X)⟦s⟧)
      (𝟙 ((perfectDGModuleToDerived A D S).obj
        ((perfectDGModuleShiftDG A D S s).onHomotopy.obj X)) ≫
        (perfectDGModuleShiftHomotopyDerivedIso A D S s).hom.app X ≫
        ((modulePerfectOver A D S).ι.commShiftIso s).inv.app
          ((perfectDGModuleToPerfect A D S).obj X))).hom =
      (perfectDGModuleShiftHomotopyDerivedIso A D S s).hom.app X ≫
        ((modulePerfectOver A D S).ι.commShiftIso s).inv.app
          ((perfectDGModuleToPerfect A D S).obj X) by
    simpa [perfectDGModuleShiftHomotopyPerfectIso, Functor.FullyFaithful.preimageIso,
      Functor.FullyFaithful.whiskeringRight, perfectDGModuleToPerfectCompInclusion,
      ObjectProperty.liftCompιIso] using h
  exact ((Functor.FullyFaithful.ofFullyFaithful (modulePerfectOver A D S).ι).map_preimage
      (X := (perfectDGModuleToPerfect A D S).obj
        ((perfectDGModuleShiftDG A D S s).onHomotopy.obj X))
      (Y := ((perfectDGModuleToPerfect A D S).obj X)⟦s⟧)
      (𝟙 _ ≫ (perfectDGModuleShiftHomotopyDerivedIso A D S s).hom.app X ≫
        ((modulePerfectOver A D S).ι.commShiftIso s).inv.app
          ((perfectDGModuleToPerfect A D S).obj X))).trans (Category.id_comp _)

end SerrePositivity.DifferentialGraded
end

end EnhancementShiftComparison

/-! ## EnhancementShift（旧 SerrePositivity/DifferentialGraded/Perfect/EnhancementShift.lean） -/

/-! # 実際のdg shiftによる射影的perfect H⁰の整数shift

主Perfとの完全忠実同値を使い、各整数の実際のdg shiftのH⁰にzero/add coherenceを誘導する。
-/

@[expose] public section EnhancementShift
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- Perf同値の逆関手と実際のdg shiftのH⁰との自然比較を、順関手の完全忠実性で引き戻す。 -/
def perfectDGModuleInverseShiftIso (S : Set D) (s : ℤ) :
    (perfectDGModuleHomotopyEquivalence A D S).inverse ⋙
      (perfectDGModuleShiftDG A D S s).onHomotopy ≅
    shiftFunctor (PerfectModuleCategoryOver A D S) s ⋙
      (perfectDGModuleHomotopyEquivalence A D S).inverse := by
  let e := perfectDGModuleHomotopyEquivalence A D S
  exact ((Functor.FullyFaithful.ofFullyFaithful e.functor).whiskeringRight
    (PerfectModuleCategoryOver A D S)).preimageIso
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft e.inverse (perfectDGModuleShiftHomotopyPerfectIso A D S s) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight e.counitIso (shiftFunctor (PerfectModuleCategoryOver A D S) s) ≪≫
        (shiftFunctor (PerfectModuleCategoryOver A D S) s).leftUnitor ≪≫
        (shiftFunctor (PerfectModuleCategoryOver A D S) s).rightUnitor.symm ≪≫
        Functor.isoWhiskerLeft (shiftFunctor (PerfectModuleCategoryOver A D S) s)
          e.counitIso.symm ≪≫
        (Functor.associator _ _ _).symm)

/-- 実際のdg shiftのH⁰に、Mathlibの誘導shift構造でzero/addとその整合性を与える。 -/
instance perfectDGHomotopyHasShift (S : Set D) :
    HasShift (PerfectDGHomotopyCategoryOver A D S) ℤ :=
  (Functor.FullyFaithful.ofFullyFaithful (perfectDGModuleToPerfect A D S)).hasShift
    (fun s => (perfectDGModuleShiftDG A D S s).onHomotopy)
    (perfectDGModuleShiftHomotopyPerfectIso A D S)

/-- 各整数の誘導shift関手は、実際の全Hom dg shiftからのH⁰関手そのものである。 -/
lemma perfectDGHomotopy_shiftFunctor (S : Set D) (s : ℤ) :
    shiftFunctor (PerfectDGHomotopyCategoryOver A D S) s =
      (perfectDGModuleShiftDG A D S s).onHomotopy := rfl

/-- H⁰ shiftの加法性は元のdg関手が誘導するH⁰加法性から継承する。 -/
instance perfectDGHomotopyShiftAdditive (S : Set D) (s : ℤ) :
    (shiftFunctor (PerfectDGHomotopyCategoryOver A D S) s).Additive := by
  rw [perfectDGHomotopy_shiftFunctor]
  infer_instance

/-- 完全忠実比較により誘導したshiftの下で、順関手の比較を元の自然同型として公開する。 -/
instance perfectDGModuleHomotopyEquivalenceFunctorCommShift (S : Set D) :
    (perfectDGModuleHomotopyEquivalence A D S).functor.CommShift ℤ :=
  Functor.CommShift.ofHasShiftOfFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful (perfectDGModuleToPerfect A D S))
    (fun s => (perfectDGModuleShiftDG A D S s).onHomotopy)
    (perfectDGModuleShiftHomotopyPerfectIso A D S)

/-- 順関手の整合的比較から、逆関手の比較をMathlibの随伴APIで構成する。 -/
instance perfectDGModuleHomotopyEquivalenceInverseCommShift (S : Set D) :
    (perfectDGModuleHomotopyEquivalence A D S).inverse.CommShift ℤ :=
  (perfectDGModuleHomotopyEquivalence A D S).commShiftInverse ℤ

/-- Perfとの同値の単位・余単位も整数shiftと整合する。 -/
instance perfectDGModuleHomotopyEquivalenceCommShift (S : Set D) :
    (perfectDGModuleHomotopyEquivalence A D S).CommShift ℤ :=
  (perfectDGModuleHomotopyEquivalence A D S).commShift_of_functor ℤ

/-- 元のH⁰比較関手も、実際のdg shiftから誘導した整数shiftと整合する。 -/
instance perfectDGModuleToPerfectCommShift (S : Set D) :
    (perfectDGModuleToPerfect A D S).CommShift ℤ :=
  perfectDGModuleHomotopyEquivalenceFunctorCommShift A D S

/-- 主Perfへの整合的shift比較は、実際のdg shiftから構成した自然同型そのものである。 -/
lemma perfectDGModuleToPerfect_commShiftIso (S : Set D) (s : ℤ) :
    (perfectDGModuleToPerfect A D S).commShiftIso s =
      perfectDGModuleShiftHomotopyPerfectIso A D S s := rfl

end SerrePositivity.DifferentialGraded
end

end EnhancementShift

/-! ## EnhancementTriangulated（旧 SerrePositivity/DifferentialGraded/Perfect/EnhancementTriangulated.lean） -/

/-! # 実際のdg shiftを備えたperfect H⁰の三角構造

構成済みの線形・shift同値で主Perfの三角構造を引き戻す。
標準dg cone三角形との比較と、小さい代表系への移送は別に検証する。
-/

@[expose] public section EnhancementTriangulated
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 主Perfの零対象を同値の逆関手で運び、H⁰に零対象を与える。 -/
instance perfectDGHomotopyHasZeroObject (S : Set D) :
    HasZeroObject (PerfectDGHomotopyCategoryOver A D S) :=
  dgComparisonHasZeroObject (perfectDGModuleHomotopyEquivalence A D S)

/-- 主Perfでdistinguishedとなる三角形を引き戻し、既存の実際のdg shiftの下で各公理を満たす。 -/
instance perfectDGHomotopyPretriangulated (S : Set D) :
    Pretriangulated (PerfectDGHomotopyCategoryOver A D S) :=
  dgComparisonPretriangulated (perfectDGModuleHomotopyEquivalence A D S)

/-- H⁰の三角形のdistinguished性は、主Perfにおける比較像で判定できる。 -/
lemma perfectDGHomotopy_distinguished_iff (S : Set D)
    (T : Triangle (PerfectDGHomotopyCategoryOver A D S)) :
    T ∈ distTriang (PerfectDGHomotopyCategoryOver A D S) ↔
      (perfectDGModuleToPerfect A D S).mapTriangle.obj T ∈
        distTriang (PerfectModuleCategoryOver A D S) := Iff.rfl

/-- 主Perfへの比較は三角関手。distinguishedクラスの引き戻しの定義から従う。 -/
instance perfectDGModuleToPerfectIsTriangulated (S : Set D) :
    (perfectDGModuleToPerfect A D S).IsTriangulated where
  map_distinguished _ hT := hT

/-- 主Perfへの完全忠実三角関手から、八面体公理を反映する。 -/
instance perfectDGHomotopyIsTriangulated (S : Set D) :
    IsTriangulated (PerfectDGHomotopyCategoryOver A D S) :=
  IsTriangulated.of_fully_faithful_triangulated_functor (perfectDGModuleToPerfect A D S)

/-- H⁰と主Perfの同値は、整数shiftに整合する三角同値である。 -/
instance perfectDGModuleHomotopyEquivalenceIsTriangulated (S : Set D) :
    (perfectDGModuleHomotopyEquivalence A D S).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (by
    change (perfectDGModuleToPerfect A D S).IsTriangulated
    infer_instance)

end SerrePositivity.DifferentialGraded
end

end EnhancementTriangulated

/-! ## EnhancementCone（旧 SerrePositivity/DifferentialGraded/Perfect/EnhancementCone.lean） -/

/-! # 射影的perfect dg加群の実際の標準cone三角形

Hom複体を共有する充満dg部分圏の射を使い、元のmoduleCone・包含・connecting射をH⁰へ運ぶ。
この三角形のdistinguished性は比較のshift整合性を確認した後に証明する。
-/

@[expose] public section EnhancementCone
universe u v w w'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end EnhancementCone

/-! ## EnhancementDerivedComparison（旧 SerrePositivity/DifferentialGraded/Perfect/EnhancementDerivedComparison.lean） -/

/-! # perfect dg H⁰から主導来圏への整合的三角比較 -/

@[expose] public section EnhancementDerivedComparison
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 主導来比較の整数shiftを、主Perf比較と既存包含の合成から自然同型で運ぶ。 -/
instance perfectDGModuleToDerivedCommShift (S : Set D) :
    (perfectDGModuleToDerived A D S).CommShift ℤ :=
  Functor.CommShift.ofIso (perfectDGModuleToPerfectCompInclusion A D S) ℤ

/-- 主Perf経由の因子化の自然同型もshiftに整合する。 -/
instance perfectDGModuleToPerfectCompInclusionCommShift (S : Set D) :
    NatTrans.CommShift (perfectDGModuleToPerfectCompInclusion A D S).hom ℤ :=
  Functor.CommShift.ofIso_compatibility (perfectDGModuleToPerfectCompInclusion A D S) ℤ

/-- 主導来比較は三角関手。主Perf比較と既存三角包含の合成から運ぶ。 -/
instance perfectDGModuleToDerivedIsTriangulated (S : Set D) :
    (perfectDGModuleToDerived A D S).IsTriangulated := by
  have : (perfectDGModuleToPerfect A D S ⋙ perfectModuleInclusion A D S).IsTriangulated :=
    inferInstance
  exact Functor.isTriangulated_of_iso (perfectDGModuleToPerfectCompInclusion A D S)

/-- 主導来比較の整合的shiftは、実際のdg shiftから構成した比較と各対象で一致する。 -/
lemma perfectDGModuleToDerived_commShiftIso_hom_app (S : Set D) (s : ℤ)
    (X : PerfectDGHomotopyCategoryOver A D S) :
    ((perfectDGModuleToDerived A D S).commShiftIso s).hom.app X =
      (perfectDGModuleShiftHomotopyDerivedIso A D S s).hom.app X := by
  simp only [Functor.CommShift.ofIso_commShiftIso_hom_app,
    Functor.commShiftIso_comp_hom_app, perfectDGModuleToPerfect_commShiftIso,
    perfectDGModuleToPerfectCompInclusion, ObjectProperty.liftCompιIso,
    Iso.refl_inv, Iso.refl_hom, NatTrans.id_app]
  change 𝟙 ((modulePerfectOver A D S).ι.obj ((perfectDGModuleToPerfect A D S).obj
      ((perfectDGModuleShiftDG A D S s).onHomotopy.obj X))) ≫
    ((modulePerfectOver A D S).ι.map
      ((perfectDGModuleShiftHomotopyPerfectIso A D S s).hom.app X) ≫
      ((modulePerfectOver A D S).ι.commShiftIso s).hom.app
        ((perfectDGModuleToPerfect A D S).obj X)) ≫
      (shiftFunctor (DerivedModuleCategory A D) s).map
        (𝟙 ((modulePerfectOver A D S).ι.obj ((perfectDGModuleToPerfect A D S).obj X))) = _
  simp only [Category.id_comp]
  rw [perfectDGModuleShiftHomotopyPerfectIso_hom_inclusion]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  let Y : DerivedModuleCategory A D := (perfectDGModuleToDerived A D S).obj X
  have h : (shiftFunctor (DerivedModuleCategory A D) s).map (𝟙 Y) = 𝟙 (Y⟦s⟧) :=
    (shiftFunctor (DerivedModuleCategory A D) s).map_id Y
  exact (congrArg (fun a => (perfectDGModuleShiftHomotopyDerivedIso A D S s).hom.app X ≫ a)
    ((Category.id_comp _).trans h)).trans (Category.comp_id _)

end SerrePositivity.DifferentialGraded
end

end EnhancementDerivedComparison

/-! ## EnhancementShiftEvaluation（旧 SerrePositivity/DifferentialGraded/Perfect/EnhancementShiftEvaluation.lean） -/

/-! # 実際の閉零代表におけるperfect dg shift比較の計算 -/

@[expose] public section EnhancementShiftEvaluation
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 包含のshift比較は任意のH⁰対象で、全加群のshift比較の成分となる。 -/
lemma perfectDGModuleShiftHomotopyInclusionIso_hom_app (S : Set D) (s : ℤ)
    (X : PerfectDGHomotopyCategoryOver A D S) :
    (perfectDGModuleShiftHomotopyInclusionIso A D S s).hom.app X =
      (moduleShiftDGHomotopyIso A D s).hom.app
        ((perfectDGModuleInclusion A D S).onHomotopy.obj X) :=
  restrictHomotopyComparison_hom_app (moduleShiftDG A D s) (modulePerfectProjectiveOver A D S)
    (fun _ h => modulePerfectProjectiveOver_shift A D h s)
    (shiftFunctor (ModuleHomotopyCategory A D) s) (moduleShiftDGHomotopyIso A D s) X


/-- perfect dg shiftと包含の比較は、実際の加群代表で商関手のshift比較を返す。 -/
lemma perfectDGModuleShiftHomotopyInclusionIso_hom_obj (S : Set D) (s : ℤ)
    (M : PerfectDGModuleOver A D S) :
    (perfectDGModuleShiftHomotopyInclusionIso A D S s).hom.app
        (perfectDGModuleHomotopyObj A D S M) =
      ((moduleToHomotopy A D).commShiftIso s).hom.app (ForgetEnrichment.of (Complex A) M.val) :=
  (perfectDGModuleShiftHomotopyInclusionIso_hom_app A D S s _).trans
    (moduleShiftDGHomotopyIso_closed_hom_app A D s (ForgetEnrichment.of (Complex A) M.val))

/-- 主導来shift比較は閉零代表上で、既存のK(D)経由の合成関手のshift比較に一致する。 -/
lemma perfectDGModuleShiftHomotopyDerivedIso_hom_obj (S : Set D) (s : ℤ)
    (M : PerfectDGModuleOver A D S) :
    (perfectDGModuleShiftHomotopyDerivedIso A D S s).hom.app
        (perfectDGModuleHomotopyObj A D S M) =
      ((moduleToHomotopy A D ⋙ moduleHomotopyToDerivedClosed A D).commShiftIso s).hom.app
        (ForgetEnrichment.of (Complex A) M.val) := by
  have h := comparisonCompose_hom_app
    (perfectDGModuleShiftDG A D S s).onHomotopy (perfectDGModuleInclusion A D S).onHomotopy
    (moduleHomotopyToDerivedClosed A D) (shiftFunctor (ModuleHomotopyCategory A D) s)
    (shiftFunctor (DerivedModuleCategory A D) s)
    (perfectDGModuleShiftHomotopyInclusionIso A D S s)
    ((moduleHomotopyToDerivedClosed A D).commShiftIso s) (perfectDGModuleHomotopyObj A D S M)
  let Y : ModuleCategory A D := ForgetEnrichment.of (Complex A) M.val
  have h' := congrArg (fun a => (moduleHomotopyToDerivedClosed A D).map a ≫
    ((moduleHomotopyToDerivedClosed A D).commShiftIso s).hom.app ((moduleToHomotopy A D).obj Y))
    (perfectDGModuleShiftHomotopyInclusionIso_hom_obj A D S s M)
  exact h.trans (h'.trans (Functor.commShiftIso_comp_hom_app
    (moduleToHomotopy A D) (moduleHomotopyToDerivedClosed A D) s Y).symm)

end SerrePositivity.DifferentialGraded
end

end EnhancementShiftEvaluation

/-! ## EnhancementConeComparison（旧 SerrePositivity/DifferentialGraded/Perfect/EnhancementConeComparison.lean） -/

/-! # 実際のperfect dg cone三角形と主導来三角構造の一致 -/

@[expose] public section EnhancementConeComparison
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 実際のconnecting射の主導来比較は、整合的shiftと標準比較同型で可換となる。 -/
lemma perfectDGModuleConeConnecting_toDerived (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    ((perfectDGModuleToDerived A D S).map
      (perfectDGModuleHomotopyMap A D S
        (M := perfectDGModuleCone A D S M N f) (N := perfectDGModuleShiftObj A D S 1 M)
        (moduleConeConnecting A D f)) ≫
      ((perfectDGModuleToDerived A D S).commShiftIso (1 : ℤ)).hom.app
        (perfectDGModuleHomotopyObj A D S M)) ≫
      ((moduleToHomotopyDerivedIso A D).hom.app
        (ForgetEnrichment.of (Complex A) M.val))⟦(1 : ℤ)⟧' =
    (moduleToHomotopyDerivedIso A D).hom.app (moduleCone A D f) ≫
      (moduleToDerived A D).map (moduleConeConnecting A D f) ≫
      ((moduleToDerived A D).commShiftIso (1 : ℤ)).hom.app
        (ForgetEnrichment.of (Complex A) M.val) := by
  let X : ModuleCategory A D := ForgetEnrichment.of (Complex A) M.val
  let F := perfectDGModuleToDerived A D S
  let g := perfectDGModuleHomotopyMap A D S
    (M := perfectDGModuleCone A D S M N f) (N := perfectDGModuleShiftObj A D S 1 M)
    (moduleConeConnecting A D f)
  let e := moduleToHomotopyDerivedIso A D
  have hs := (perfectDGModuleToDerived_commShiftIso_hom_app A D S (1 : ℤ)
    (perfectDGModuleHomotopyObj A D S M)).trans
      (perfectDGModuleShiftHomotopyDerivedIso_hom_obj A D S (1 : ℤ) M)
  have hn := NatTrans.shift_app_comm e.hom (1 : ℤ) X
  have hm := perfectDGModuleHomotopyMap_toDerived A D S
    (M := perfectDGModuleCone A D S M N f) (N := perfectDGModuleShiftObj A D S 1 M)
    (moduleConeConnecting A D f)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => F.map g ≫ a)
      ((congrArg (fun a => a ≫ (e.hom.app X)⟦(1 : ℤ)⟧') hs).trans hn)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun a => a ≫ ((moduleToDerived A D).commShiftIso (1 : ℤ)).hom.app X) hm).trans
          (Category.assoc _ _ _))))

/-- 主導来関手で写した標準三角形の第三射を、実際のconnecting射で計算する。 -/
lemma perfectDGModuleConeTriangle_toDerived_mor₃ (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    ((perfectDGModuleToDerived A D S).mapTriangle.obj
      (perfectDGModuleConeTriangle A D S M N f)).mor₃ =
    (perfectDGModuleToDerived A D S).map
      (perfectDGModuleHomotopyMap A D S
        (M := perfectDGModuleCone A D S M N f) (N := perfectDGModuleShiftObj A D S 1 M)
        (moduleConeConnecting A D f)) ≫
      ((perfectDGModuleToDerived A D S).commShiftIso (1 : ℤ)).hom.app
        (perfectDGModuleHomotopyObj A D S M) :=
  perfectDGModuleConeTriangle_map_mor₃ A D S (perfectDGModuleToDerived A D S) M N f


/-- 実際のdg cone三角形の主導来像は、元の加群の主導来cone三角形と同型である。 -/
def perfectDGModuleConeTriangleToDerivedIso (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    (perfectDGModuleToDerived A D S).mapTriangle.obj (perfectDGModuleConeTriangle A D S M N f) ≅
      moduleDerivedConeTriangle A D f := by
  let e := moduleToHomotopyDerivedIso A D
  refine Triangle.isoMk _ _ (e.app (ForgetEnrichment.of (Complex A) M.val))
    (e.app (ForgetEnrichment.of (Complex A) N.val)) (e.app (moduleCone A D f)) ?_ ?_ ?_
  · exact perfectDGModuleHomotopyMap_toDerived A D S f
  · exact perfectDGModuleHomotopyMap_toDerived A D S
      (M := N) (N := perfectDGModuleCone A D S M N f) (moduleConeInr A D f)
  · exact (congrArg (fun a => a ≫ (e.hom.app (ForgetEnrichment.of (Complex A) M.val))⟦(1 : ℤ)⟧')
      (perfectDGModuleConeTriangle_toDerived_mor₃ A D S M N f)).trans
        (perfectDGModuleConeConnecting_toDerived A D S M N f)

/-- 実際の標準dg cone三角形は、構成したH⁰三角構造でdistinguishedである。 -/
lemma perfectDGModuleConeTriangle_distinguished (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    perfectDGModuleConeTriangle A D S M N f ∈ distTriang (PerfectDGHomotopyCategoryOver A D S) := by
  apply ((perfectDGModuleToDerived A D S).map_distinguished_iff _).mp
  exact isomorphic_distinguished _ (moduleDerivedConeTriangle_distinguished A D f) _
    (perfectDGModuleConeTriangleToDerivedIso A D S M N f)

/-- 閉零部分圏の射からのH⁰像を、全加群への包含を経由した像から復元する。 -/
lemma perfectDGModuleHomotopyMap_onClosed (S : Set D)
    {X Y : ClosedCategory A (PerfectDGModuleOver A D S)} (f : X ⟶ Y) :
    perfectDGModuleHomotopyMap A D S
      (M := ForgetEnrichment.to (Complex A) X) (N := ForgetEnrichment.to (Complex A) Y)
      ((perfectDGModuleInclusion A D S).onClosed.map f) =
    (toHomotopy A (PerfectDGModuleOver A D S)).map f :=
  congrArg (fun g => (toHomotopy A (PerfectDGModuleOver A D S)).map g)
    ((perfectDGModuleInclusion A D S).onClosed.preimage_map f)

/-- H⁰のdistinguished三角形は、実際の射影的perfect dg加群の標準cone三角形の同型閉包である。 -/
lemma perfectDGHomotopy_distinguished_iff_cone (S : Set D)
    (T : Triangle (PerfectDGHomotopyCategoryOver A D S)) :
    T ∈ distTriang (PerfectDGHomotopyCategoryOver A D S) ↔
      ∃ (M N : PerfectDGModuleOver A D S)
        (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val),
        Nonempty (T ≅ perfectDGModuleConeTriangle A D S M N f) := by
  constructor
  · intro hT
    let M : PerfectDGModuleOver A D S := ForgetEnrichment.to (Complex A) T.obj₁.as
    let N : PerfectDGModuleOver A D S := ForgetEnrichment.to (Complex A) T.obj₂.as
    obtain ⟨f, hf⟩ := (toHomotopy A (PerfectDGModuleOver A D S)).map_surjective T.mor₁
    let g : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val :=
      (perfectDGModuleInclusion A D S).onClosed.map f
    have hg : (perfectDGModuleConeTriangle A D S M N g).mor₁ = T.mor₁ :=
      (perfectDGModuleHomotopyMap_onClosed A D S f).trans hf
    have he : Arrow.mk (perfectDGModuleConeTriangle A D S M N g).mor₁ ≅ Arrow.mk T.mor₁ :=
      Arrow.isoMk' _ _ (Iso.refl T.obj₁) (Iso.refl T.obj₂)
        ((Category.id_comp _).trans (hg.symm.trans (Category.comp_id _).symm))
    obtain ⟨e, _⟩ := exists_iso_of_arrow_iso (perfectDGModuleConeTriangle A D S M N g) T
      (perfectDGModuleConeTriangle_distinguished A D S M N g) hT he
    exact ⟨M, N, g, ⟨e.symm⟩⟩
  · rintro ⟨M, N, f, ⟨e⟩⟩
    exact isomorphic_distinguished _ (perfectDGModuleConeTriangle_distinguished A D S M N f) _ e

end SerrePositivity.DifferentialGraded
end

end EnhancementConeComparison
