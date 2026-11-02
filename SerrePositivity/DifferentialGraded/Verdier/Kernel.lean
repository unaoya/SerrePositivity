module

public import SerrePositivity.DifferentialGraded.Verdier.Scalar
public import SerrePositivity.DifferentialGraded.Verdier.Karoubi
public import SerrePositivity.DifferentialGraded.Morita.Perfect
public import SerrePositivity.DifferentialGraded.Verdier.Derived
public import SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceGraph
public import SerrePositivity.DifferentialGraded.Morita.Kernel

/-!
# Verdier.Kernel

## 概要
11 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## ScalarDirectCompletion（旧 SerrePositivity/DifferentialGraded/Verdier/ScalarDirectCompletion.lean） -/

/-! # 直接局所化した係数変更の Karoubi 完備化と局所 perfect 比較 -/

@[expose] public section ScalarDirectCompletion
universe u v

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory CategoryTheory.Functor Idempotents ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D] (S : Set D)

/-- 元の係数変更を先に Verdier 局所化した関手の、実際の Karoubi 延長。 -/
def sourceScalarCompletedFunctor :
    CompletedTriaQuotient A D S ⥤ CompletedTriaQuotient A' (DGBaseChange φ D) S :=
  (functorExtension₂ _ _).obj (sourceScalarVerdierFunctor φ D S)

instance sourceScalarCompletedFunctorCommShift :
    (sourceScalarCompletedFunctor φ D S).CommShift ℤ := by
  dsimp [sourceScalarCompletedFunctor]
  infer_instance
instance sourceScalarCompletedFunctorIsTriangulated :
    (sourceScalarCompletedFunctor φ D S).IsTriangulated := by
  dsimp [sourceScalarCompletedFunctor]
  infer_instance

/-- 未完備の指定商からの標準包含と、直接局所化の完備化との正方形。 -/
def sourceScalarCompletedFactors :
    toKaroubi (TriaQuotient A D S) ⋙ sourceScalarCompletedFunctor φ D S ≅
      sourceScalarVerdierFunctor φ D S ⋙ toKaroubi (TriaQuotient A' (DGBaseChange φ D) S) :=
  karoubiFactor (sourceScalarVerdierFunctor φ D S)

instance sourceScalarCompletedFactorsCommShift :
    NatTrans.CommShift (sourceScalarCompletedFactors φ D S).hom ℤ :=
  karoubiFactorCommShift _

def sourceScalarCompletedFactorsTriangle :=
  Functor.mapTriangleIso (sourceScalarCompletedFactors φ D S)

variable (h : localKFlat A D S) (h' : localKFlat A' (DGBaseChange φ D) S)

/-- 直接局所化と局所同値による輸送の比較を、実際の Karoubi 延長で完備化する。 -/
def sourceScalarCompletedTransportIso :
    sourceScalarCompletedFunctor φ D S ≅ scalarCompletedTriaFunctor φ D S h h' :=
  (functorExtension₂ _ _).mapIso (sourceScalarLocalTransportIso φ D S h h')

/-- 完備化した直接局所化と、明示的 dg 商側の tria の係数変更との正方形。 -/
def sourceScalarCompletedTriaSquare :
    sourceScalarCompletedFunctor φ D S ⋙
        (localCompletedQuotientEquivalence A' (DGBaseChange φ D) S h').functor ≅
      (localCompletedQuotientEquivalence A D S h).functor ⋙
        (functorExtension₂ _ _).obj (quotientScalarTriaFunctor φ S) :=
  karoubiFunctorSquare _ _ (sourceScalarLocalQuotientSquare φ D S)

/-- 全 tria–Perf 比較を用いた、直接局所化の完備化と実際の Perf 係数変更の正方形。 -/
def sourceScalarCompletedPerfectSquare :
    sourceScalarCompletedFunctor φ D S ⋙
        (graphCompletedPerfectComparison A' (DGBaseChange φ D) S h').functor ≅
      (graphCompletedPerfectComparison A D S h).functor ⋙ quotientScalarPerfectFunctor φ D S :=
  (associator _ _ _).symm ≪≫
    isoWhiskerRight (sourceScalarCompletedTriaSquare φ D S h h') _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft _ (quotientScalarKaroubiPerfectSquare φ S) ≪≫ (associator _ _ _).symm

/-- 直接局所化の完備化は、既存の局所 perfect enhancement 比較とも可換する。 -/
def sourceScalarCompletedLocalPerfectSquare :
    (localPerfectQuotientEquivalence A D S h).functor ⋙ sourceScalarCompletedFunctor φ D S ≅
      quotientScalarPerfectHomotopyFunctor φ D S ⋙
        (localPerfectQuotientEquivalence A' (DGBaseChange φ D) S h').functor :=
  isoWhiskerLeft _ (sourceScalarCompletedTransportIso φ D S h h') ≪≫
    scalarCompletedLocalPerfectSquare φ D S h h'

/-- 直接局所化した完備係数変更と、以前の完備 perfect 輸送経路の同定。 -/
def sourceScalarCompletionComparisonIso :
    sourceScalarCompletedFunctor φ D S ≅ completedScalarExtension φ D S h h' :=
  sourceScalarCompletedTransportIso φ D S h h' ≪≫ scalarCompletionComparisonIso φ D S h h'
end SerrePositivity.DifferentialGraded.DGQuotient
end

end ScalarDirectCompletion

/-! ## KernelLocalPerfectSquare（旧 SerrePositivity/DifferentialGraded/Verdier/KernelLocalPerfectSquare.lean） -/

/-! # 一般 kernel から誘導した商作用と既存局所 perfect enhancement 比較の正方形

主 Perf の実作用を先に局所化し、指定商の同値を通して H⁰ へ運ぶ。
この H⁰ の運搬だけから新しい dg 関手の存在を結論しない。
-/

@[expose] public section KernelLocalPerfectSquare
universe u v w

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory CategoryTheory.Functor Idempotents Morita
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (S : Set D) (hD : localKFlat A D S)

/-- 指定 Perf 商へ表示し直した局所同値は、元の局所 perfect 比較へ戻る。 -/
def localPerfectVerdierFactors :
    (localPerfectToPerfectVerdierEquivalence A D S hD).functor ⋙
        (perfectCompletedToTriaQuotientEquivalence A D S).functor ≅
      (localPerfectQuotientEquivalence A D S hD).functor :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (perfectCompletedToTriaQuotientEquivalence A D S).counitIso ≪≫
      Functor.rightUnitor _

instance localPerfectVerdierFactorsCommShift :
    NatTrans.CommShift (localPerfectVerdierFactors A D S hD).hom ℤ := by
  dsimp only [localPerfectVerdierFactors, Iso.trans_hom, isoWhiskerLeft_hom]
  infer_instance

variable (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)
  (hK : kernelColumnsPerfect A D E K) (T : Set E)
  (hST : ∀ d ∈ S, modulePerfectOver A E T ((kernelDerivedColumn A D E d).obj K))
  (hE : localKFlat A E T)

instance perfectKernelCompletedVerdierFunctorCommShift :
    (perfectKernelCompletedVerdierFunctor A D E K hK S T hST).CommShift ℤ := by
  dsimp [perfectKernelCompletedVerdierFunctor]
  infer_instance
instance perfectKernelCompletedVerdierFunctorIsTriangulated :
    (perfectKernelCompletedVerdierFunctor A D E K hK S T hST).IsTriangulated := by
  dsimp [perfectKernelCompletedVerdierFunctor]
  infer_instance

/-- 一般 kernel の実際の Perf 作用の局所化を、指定完備 tria 商へ表示する。 -/
def mainKernelCompletedQuotientFunctor :
    CompletedTriaQuotient A D S ⥤ CompletedTriaQuotient A E T :=
  (perfectCompletedToTriaQuotientEquivalence A D S).inverse ⋙
    perfectKernelCompletedVerdierFunctor A D E K hK S T hST ⋙
      (perfectCompletedToTriaQuotientEquivalence A E T).functor

instance mainKernelCompletedQuotientFunctorCommShift :
    (mainKernelCompletedQuotientFunctor A D S E K hK T hST).CommShift ℤ := by
  dsimp [mainKernelCompletedQuotientFunctor]
  infer_instance
instance mainKernelCompletedQuotientFunctorIsTriangulated :
    (mainKernelCompletedQuotientFunctor A D S E K hK T hST).IsTriangulated := by
  dsimp [mainKernelCompletedQuotientFunctor]
  infer_instance

/-- 実際に局所化した kernel 作用を、商の perfect enhancement の H⁰ に運ぶ。 -/
def mainKernelQuotientPerfectHomotopyFunctor :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ⥤
      PerfectDGHomotopyCategoryOver A (QuotientObject E T) Set.univ :=
  (localPerfectToPerfectVerdierEquivalence A D S hD).functor ⋙
    perfectKernelCompletedVerdierFunctor A D E K hK S T hST ⋙
      (localPerfectToPerfectVerdierEquivalence A E T hE).inverse

instance mainKernelQuotientPerfectHomotopyFunctorCommShift :
    (mainKernelQuotientPerfectHomotopyFunctor A D S hD E K hK T hST hE).CommShift ℤ := by
  dsimp [mainKernelQuotientPerfectHomotopyFunctor]
  infer_instance
instance mainKernelQuotientPerfectHomotopyFunctorIsTriangulated :
    (mainKernelQuotientPerfectHomotopyFunctor A D S hD E K hK T hST hE).IsTriangulated := by
  dsimp [mainKernelQuotientPerfectHomotopyFunctor]
  infer_instance

def mainKernelPerfectVerdierSquare :
    mainKernelQuotientPerfectHomotopyFunctor A D S hD E K hK T hST hE ⋙
        (localPerfectToPerfectVerdierEquivalence A E T hE).functor ≅
      (localPerfectToPerfectVerdierEquivalence A D S hD).functor ⋙
        perfectKernelCompletedVerdierFunctor A D E K hK S T hST :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (localPerfectToPerfectVerdierEquivalence A E T hE).counitIso ≪≫
      Functor.rightUnitor _)

instance mainKernelPerfectVerdierSquareCommShift :
    NatTrans.CommShift (mainKernelPerfectVerdierSquare A D S hD E K hK T hST hE).hom ℤ := by
  dsimp only [mainKernelPerfectVerdierSquare, Iso.trans_hom, isoWhiskerLeft_hom]
  infer_instance

/-- 一般主導来 kernel と既存の局所 perfect enhancement 比較そのものの正方形。 -/
def mainKernelLocalPerfectSquare :
    (localPerfectQuotientEquivalence A D S hD).functor ⋙
        mainKernelCompletedQuotientFunctor A D S E K hK T hST ≅
      mainKernelQuotientPerfectHomotopyFunctor A D S hD E K hK T hST hE ⋙
        (localPerfectQuotientEquivalence A E T hE).functor :=
  (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (mainKernelPerfectVerdierSquare A D S hD E K hK T hST hE).symm _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (localPerfectVerdierFactors A E T hE)

instance mainKernelLocalPerfectSquareCommShift :
    NatTrans.CommShift (mainKernelLocalPerfectSquare A D S hD E K hK T hST hE).hom ℤ := by
  dsimp only [mainKernelLocalPerfectSquare, Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom]
  infer_instance

def mainKernelLocalPerfectSquareTriangle :=
  Functor.mapTriangleIso (mainKernelLocalPerfectSquare A D S hD E K hK T hST hE)
end SerrePositivity.DifferentialGraded.DGQuotient
end

end KernelLocalPerfectSquare

/-! ## KernelQuotientNaturality（旧 SerrePositivity/DifferentialGraded/Verdier/KernelQuotientNaturality.lean） -/

/-! # 許容する主導来 kernel の全射に自然な指定 Verdier 作用

元の Perf 作用の kernel 関手性を、実際の指定局所化へ降ろす。
-/

@[expose] public section KernelQuotientNaturality
universe u v w

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents Morita
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (S : Set D) (T : Set E)

/-- 全列が perfect で、指定 S の列が Perf_T に入る kernel。射には追加条件を課さない。 -/
def supportedPerfectKernels : ObjectProperty (Kernel A D E) := fun K =>
  kernelColumnsPerfect A D E K ∧
    ∀ d ∈ S, modulePerfectOver A E T ((kernelDerivedColumn A D E d).obj K)

abbrev SupportedPerfectKernelCategory := (supportedPerfectKernels A D E S T).FullSubcategory

/-- 許容 kernel の充満部分圏から、U16 の全 perfect 列 kernel の充満部分圏への包含。 -/
def supportedPerfectKernelInclusion :
    SupportedPerfectKernelCategory A D E S T ⥤ (kernelColumnsPerfect A D E).FullSubcategory :=
  (kernelColumnsPerfect A D E).lift (supportedPerfectKernels A D E S T).ι
    (fun K => K.property.1)

/-- U16 の主導来 kernel 関手そのものの、指定部分圏への制限。 -/
def supportedKernelPerfectFunctor :
    SupportedPerfectKernelCategory A D E S T ⥤
      (PerfectModuleCategory A D ⥤ PerfectModuleCategory A E) :=
  supportedPerfectKernelInclusion A D E S T ⋙ perfectDerivedKernelActionFunctor A D E

variable (K : SupportedPerfectKernelCategory A D E S T)

/-- 関手部分は、元の Perf 作用を先に実際に局所化した既存の関手。 -/
abbrev supportedKernelVerdierValue :
    PerfectVerdierQuotient A D S ⥤ PerfectVerdierQuotient A E T :=
  perfectKernelVerdierFunctor A D E K.obj K.property.1 S T K.property.2

instance supportedKernelVerdierLifting :
    Localization.Lifting (perfectVerdierQuotient A D S) (perfectNullObjects A D S).trW
      ((supportedKernelPerfectFunctor A D E S T).obj K ⋙ perfectVerdierQuotient A E T)
      (supportedKernelVerdierValue A D E S T K) :=
  ⟨perfectKernelVerdierSquare A D E K.obj K.property.1 S T K.property.2⟩

variable {K} {L : SupportedPerfectKernelCategory A D E S T}

/-- 任意の主導来 kernel 射が誘導する、実際の Verdier 商関手の間の自然変換。 -/
def supportedKernelVerdierMap (f : K ⟶ L) :
    supportedKernelVerdierValue A D E S T K ⟶ supportedKernelVerdierValue A D E S T L :=
  Localization.liftNatTrans (perfectVerdierQuotient A D S) (perfectNullObjects A D S).trW
    _ _ (supportedKernelVerdierValue A D E S T K) (supportedKernelVerdierValue A D E S T L)
    (whiskerRight ((supportedKernelPerfectFunctor A D E S T).map f) (perfectVerdierQuotient A E T))

lemma supportedKernelVerdierMap_app (f : K ⟶ L) (X : PerfectModuleCategory A D) :
    (supportedKernelVerdierMap A D E S T f).app ((perfectVerdierQuotient A D S).obj X) =
      (perfectKernelVerdierSquare A D E K.obj K.property.1 S T K.property.2).hom.app X ≫
        (perfectVerdierQuotient A E T).map
          (((supportedKernelPerfectFunctor A D E S T).map f).app X) ≫
        (perfectKernelVerdierSquare A D E L.obj L.property.1 S T L.property.2).inv.app X :=
  Localization.liftNatTrans_app _ _ _ _ _ _ _ X

/-- 指定 Verdier 商への作用は、kernel の恒等射・合成を保つ関手になる。 -/
def supportedKernelVerdierFunctor :
    SupportedPerfectKernelCategory A D E S T ⥤
      (PerfectVerdierQuotient A D S ⥤ PerfectVerdierQuotient A E T) where
  obj K := supportedKernelVerdierValue A D E S T K
  map f := supportedKernelVerdierMap A D E S T f
  map_id K := by
    dsimp [supportedKernelVerdierMap]
    rw [CategoryTheory.Functor.map_id, whiskerRight_id']
    exact Localization.liftNatTrans_id _ _ _ _
  map_comp f g := by
    dsimp [supportedKernelVerdierMap]
    rw [CategoryTheory.Functor.map_comp, whiskerRight_comp]
    exact (Localization.comp_liftNatTrans _ _ _ _ _ _ _ _ _ _).symm

lemma supportedKernelVerdierMap_id (K : SupportedPerfectKernelCategory A D E S T) :
    supportedKernelVerdierMap A D E S T (𝟙 K) = 𝟙 (supportedKernelVerdierValue A D E S T K) :=
  (supportedKernelVerdierFunctor A D E S T).map_id K

lemma supportedKernelVerdierMap_comp {K L M : SupportedPerfectKernelCategory A D E S T}
    (f : K ⟶ L) (g : L ⟶ M) :
    supportedKernelVerdierMap A D E S T (f ≫ g) =
      supportedKernelVerdierMap A D E S T f ≫ supportedKernelVerdierMap A D E S T g :=
  (supportedKernelVerdierFunctor A D E S T).map_comp f g

/-- 元の Perf 作用と指定商関手の因子化正方形は、kernel の全射にも自然。 -/
def supportedKernelVerdierFactors :
    supportedKernelVerdierFunctor A D E S T ⋙
        (whiskeringLeft _ _ _).obj (perfectVerdierQuotient A D S) ≅
      supportedKernelPerfectFunctor A D E S T ⋙
        (whiskeringRight _ _ _).obj (perfectVerdierQuotient A E T) :=
  NatIso.ofComponents
    (fun K => perfectKernelVerdierSquare A D E K.obj K.property.1 S T K.property.2)
    (by
      intro K L f
      apply NatTrans.ext
      funext X
      change (supportedKernelVerdierMap A D E S T f).app
          ((perfectVerdierQuotient A D S).obj X) ≫
          (perfectKernelVerdierSquare A D E L.obj L.property.1 S T L.property.2).hom.app X = _
      rw [supportedKernelVerdierMap_app]
      simp only [Category.assoc, Iso.inv_hom_id_app]
      rfl)

/-- 同じ実際の作用を Karoubi 延長すると、kernel の射も含む完備商作用になる。 -/
def supportedKernelCompletedFunctor :
    SupportedPerfectKernelCategory A D E S T ⥤
      (Karoubi (PerfectVerdierQuotient A D S) ⥤ Karoubi (PerfectVerdierQuotient A E T)) :=
  supportedKernelVerdierFunctor A D E S T ⋙ functorExtension₂ _ _
end SerrePositivity.DifferentialGraded
end

end KernelQuotientNaturality

/-! ## KernelComparisonNaturality（旧 SerrePositivity/DifferentialGraded/Verdier/KernelComparisonNaturality.lean） -/

/-! # kernel の全射に自然な完備商・局所 perfect 比較正方形 -/

@[expose] public section KernelComparisonNaturality
universe u v w

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents Morita

private lemma conjugatedComparison_naturality
    {H V T : Type*} [Category* H] [Category* V] [Category* T]
    (e : H ≌ V) (B : V ⥤ T) (L : H ⥤ T) (p : e.functor ⋙ B ≅ L)
    {X Y : V} (f : X ⟶ Y) :
    B.map f ≫ B.map (e.counitIso.inv.app Y) ≫ p.hom.app (e.inverse.obj Y) =
      B.map (e.counitIso.inv.app X) ≫ p.hom.app (e.inverse.obj X) ≫ L.map (e.inverse.map f) := by
  have h := congrArg (fun t => B.map t ≫ p.hom.app (e.inverse.obj Y))
    (e.counitIso.inv.naturality f)
  simp only [Functor.id_map, Functor.comp_map, CategoryTheory.Functor.map_comp,
    Category.assoc] at h
  have hp := p.hom.naturality (e.inverse.map f)
  simp only [Functor.comp_map] at hp
  rw [hp] at h
  exact h

namespace DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (S : Set D) (E : Type w) [DGCategory A E] [Small.{u} E] (T : Set E)

/-- 指定完備 tria 商への実作用を、kernel の全射に対する関手として公開する。 -/
def supportedKernelCompletedTriaFunctor :
    SupportedPerfectKernelCategory A D E S T ⥤
      (CompletedTriaQuotient A D S ⥤ CompletedTriaQuotient A E T) where
  obj K := mainKernelCompletedQuotientFunctor A D S E K.obj K.property.1 T K.property.2
  map f := whiskerLeft (perfectCompletedToTriaQuotientEquivalence A D S).inverse
    (whiskerRight ((supportedKernelCompletedFunctor A D E S T).map f)
      (perfectCompletedToTriaQuotientEquivalence A E T).functor)
  map_id K := by
    rw [CategoryTheory.Functor.map_id, whiskerRight_id']
    apply NatTrans.ext
    funext X
    rfl
  map_comp f g := by
    simp only [CategoryTheory.Functor.map_comp, whiskerRight_comp, whiskerLeft_comp]

variable (hD : localKFlat A D S) (hE : localKFlat A E T)

/-- 局所 perfect enhancement の H⁰ への実作用も、全 kernel 射を含む関手になる。 -/
def supportedKernelLocalPerfectFunctor :
    SupportedPerfectKernelCategory A D E S T ⥤
      (PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ⥤
        PerfectDGHomotopyCategoryOver A (QuotientObject E T) Set.univ) where
  obj K := mainKernelQuotientPerfectHomotopyFunctor A D S hD E K.obj K.property.1 T K.property.2 hE
  map f := whiskerLeft (localPerfectToPerfectVerdierEquivalence A D S hD).functor
    (whiskerRight ((supportedKernelCompletedFunctor A D E S T).map f)
      (localPerfectToPerfectVerdierEquivalence A E T hE).inverse)
  map_id K := by
    rw [CategoryTheory.Functor.map_id, whiskerRight_id']
    apply NatTrans.ext
    funext X
    rfl
  map_comp f g := by
    simp only [CategoryTheory.Functor.map_comp, whiskerRight_comp, whiskerLeft_comp]

/-- 既存の局所 perfect 正方形そのものを、kernel の全射に自然な族へ束ねる。 -/
def supportedKernelLocalPerfectSquare :
    supportedKernelCompletedTriaFunctor A D S E T ⋙
        (whiskeringLeft _ _ _).obj (localPerfectQuotientEquivalence A D S hD).functor ≅
      supportedKernelLocalPerfectFunctor A D S E T hD hE ⋙
        (whiskeringRight _ _ _).obj (localPerfectQuotientEquivalence A E T hE).functor :=
  NatIso.ofComponents
    (fun K => mainKernelLocalPerfectSquare A D S hD E K.obj K.property.1 T K.property.2 hE)
    (by
      intro K L f
      apply NatTrans.ext
      funext X
      dsimp only [Functor.comp_map, whiskeringLeft_obj_map, whiskeringRight_obj_map,
        supportedKernelCompletedTriaFunctor, supportedKernelLocalPerfectFunctor,
        mainKernelLocalPerfectSquare, mainKernelPerfectVerdierSquare,
        Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
        isoWhiskerRight_inv, isoWhiskerLeft_inv,
        NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, associator_inv_app,
        associator_hom_app, rightUnitor_inv_app, rightUnitor_hom_app]
      simp only [Category.id_comp, Category.comp_id, Category.assoc]
      have h := conjugatedComparison_naturality
        (localPerfectToPerfectVerdierEquivalence A E T hE)
        (perfectCompletedToTriaQuotientEquivalence A E T).functor
        (localPerfectQuotientEquivalence A E T hE).functor
        (localPerfectVerdierFactors A E T hE)
        (((supportedKernelCompletedFunctor A D E S T).map f).app
          ((localPerfectToPerfectVerdierEquivalence A D S hD).functor.obj X))
      refine Eq.trans ?_ (h.trans ?_)
      · exact congrArg (fun z => (perfectCompletedToTriaQuotientEquivalence A E T).functor.map
          (((supportedKernelCompletedFunctor A D E S T).map f).app
            ((localPerfectToPerfectVerdierEquivalence A D S hD).functor.obj X)) ≫ z)
          (Category.id_comp _)
      · exact (Category.id_comp _).symm)

/-- 族の成分は、すでに公開した比較自然同型そのものである。 -/
lemma supportedKernelLocalPerfectSquare_app (K : SupportedPerfectKernelCategory A D E S T) :
    (supportedKernelLocalPerfectSquare A D S E T hD hE).app K =
      mainKernelLocalPerfectSquare A D S hD E K.obj K.property.1 T K.property.2 hE := rfl

/-- kernel 射と元の局所 perfect 正方形を貼り合わせる、自然変換の等式。 -/
lemma supportedKernelLocalPerfectSquare_naturality
    {K L : SupportedPerfectKernelCategory A D E S T} (f : K ⟶ L) :
    whiskerLeft (localPerfectQuotientEquivalence A D S hD).functor
        ((supportedKernelCompletedTriaFunctor A D S E T).map f) ≫
        (mainKernelLocalPerfectSquare A D S hD E L.obj L.property.1 T L.property.2 hE).hom =
      (mainKernelLocalPerfectSquare A D S hD E K.obj K.property.1 T K.property.2 hE).hom ≫
        whiskerRight ((supportedKernelLocalPerfectFunctor A D S E T hD hE).map f)
          (localPerfectQuotientEquivalence A E T hE).functor :=
  (supportedKernelLocalPerfectSquare A D S E T hD hE).hom.naturality f
end DGQuotient
end SerrePositivity.DifferentialGraded
end

end KernelComparisonNaturality

/-! ## KernelCompositionDescent（旧 SerrePositivity/DifferentialGraded/Verdier/KernelCompositionDescent.lean） -/

/-! # 実際の kernel 合成比較の指定商への降下

必要な局所 Hom の K-flat 条件は元の始域 D のものだけを保持する。
-/

@[expose] public section KernelCompositionDescent
universe u v w z

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents Morita
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (B : Type z) [DGCategory A B] [Small.{u} B]
  (S : Set D) (T : Set E) (U : Set B) (hD : localHomKFlat A D)
  (P : SupportedPerfectKernelCategory A D E S T)
  (Q : SupportedPerfectKernelCategory A E B T U)

lemma supportedKernelComposite_columns (d : D) (hd : d ∈ S) :
    modulePerfectOver A B U ((kernelDerivedColumn A D B d).obj
      (kernelCompose A D E B hD P.obj Q.obj)) := by
  let M := (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))
  have hP : modulePerfectOver A E T ((kernelDerivedTensor A D E P.obj).obj M) :=
    (modulePerfectOver A E T).prop_of_iso (kernelDerivedColumnActionIso A D E P.obj d).symm
      (P.property.2 d hd)
  have hQ := mainKernelAction_perfectOver A E B Q.obj T U Q.property.2 hP
  exact (modulePerfectOver A B U).prop_of_iso
    ((kernelCompositionIso A D E B hD P.obj Q.obj).app M ≪≫
      kernelDerivedColumnActionIso A D B (kernelCompose A D E B hD P.obj Q.obj) d) hQ

/-- 実際の主導来合成は、指定生成集合を対応させる許容 kernel を再び与える。 -/
def supportedKernelComposite : SupportedPerfectKernelCategory A D B S U :=
  ⟨kernelCompose A D E B hD P.obj Q.obj,
    kernelCompose_columnsPerfect_of_columns A D E B hD P.obj Q.obj P.property.1 Q.property.1,
    supportedKernelComposite_columns A D E B S T U hD P Q⟩

/-- 実際の主導来合成を許容 kernel の積圏に制限する。両 kernel の全射を保持する。 -/
def supportedKernelComposeFunctor :
    SupportedPerfectKernelCategory A D E S T × SupportedPerfectKernelCategory A E B T U ⥤
      SupportedPerfectKernelCategory A D B S U :=
  (supportedPerfectKernels A D B S U).lift
    (((supportedPerfectKernels A D E S T).ι.prod (supportedPerfectKernels A E B T U).ι) ⋙
      uncurry.obj (BimoduleTensor.derivedBimoduleComposeFunctor A B E D hD))
    (fun X => (supportedKernelComposite A D E B S T U hD X.1 X.2).property)

lemma supportedKernelComposeFunctor_map
    {X Y : SupportedPerfectKernelCategory A D E S T × SupportedPerfectKernelCategory A E B T U}
    (f : X ⟶ Y) :
    ((supportedKernelComposeFunctor A D E B S T U hD).map f).hom =
      kernelComposeMap A D E B hD f.1.hom f.2.hom := rfl

/-- 合成 kernel の Perf 作用への比較は U16a・U16d の実際の公開同型。 -/
def supportedKernelPerfectCompositionIso :
    (supportedKernelPerfectFunctor A D E S T).obj P ⋙
        (supportedKernelPerfectFunctor A E B T U).obj Q ≅
      (supportedKernelPerfectFunctor A D B S U).obj
        (supportedKernelComposite A D E B S T U hD P Q) :=
  perfectKernelCompositionIso A D E B hD P.obj Q.obj P.property.1 Q.property.1

/-- 元の Perf 合成比較は、両許容 kernel の任意の主導来射に自然。 -/
lemma supportedKernelPerfectCompositionIso_naturality
    (P' : SupportedPerfectKernelCategory A D E S T)
    (Q' : SupportedPerfectKernelCategory A E B T U) (f : P ⟶ P') (g : Q ⟶ Q') :
    NatTrans.hcomp ((supportedKernelPerfectFunctor A D E S T).map f)
        ((supportedKernelPerfectFunctor A E B T U).map g) ≫
        (supportedKernelPerfectCompositionIso A D E B S T U hD P' Q').hom =
      (supportedKernelPerfectCompositionIso A D E B S T U hD P Q).hom ≫
        perfectDerivedKernelMap A D B
          (supportedKernelComposite A D E B S T U hD P Q).property.1
          (supportedKernelComposite A D E B S T U hD P' Q').property.1
          (kernelComposeMap A D E B hD f.hom g.hom) :=
  perfectKernelCompositionIso_kernel_naturality A D E B hD P.obj Q.obj
    P.property.1 Q.property.1 P'.obj Q'.obj P'.property.1 Q'.property.1 f.hom g.hom

/-- 二つの実際の誘導商関手の合成に対する、元の Perf 上の因子化。 -/
def supportedKernelVerdierCompositeFactors :
    perfectVerdierQuotient A D S ⋙
        ((supportedKernelVerdierFunctor A D E S T).obj P ⋙
          (supportedKernelVerdierFunctor A E B T U).obj Q) ≅
      ((supportedKernelPerfectFunctor A D E S T).obj P ⋙
        (supportedKernelPerfectFunctor A E B T U).obj Q) ⋙ perfectVerdierQuotient A B U :=
  (associator _ _ _).symm ≪≫
    isoWhiskerRight (perfectKernelVerdierSquare A D E P.obj P.property.1 S T P.property.2) _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft _ (perfectKernelVerdierSquare A E B Q.obj Q.property.1 T U Q.property.2) ≪≫
    (associator _ _ _).symm

local instance supportedKernelVerdierCompositeLifting :
    Localization.Lifting (perfectVerdierQuotient A D S) (perfectNullObjects A D S).trW
      (((supportedKernelPerfectFunctor A D E S T).obj P ⋙
        (supportedKernelPerfectFunctor A E B T U).obj Q) ⋙ perfectVerdierQuotient A B U)
      ((supportedKernelVerdierFunctor A D E S T).obj P ⋙
        (supportedKernelVerdierFunctor A E B T U).obj Q) :=
  ⟨supportedKernelVerdierCompositeFactors A D E B S T U P Q⟩

local instance supportedKernelCompositionTargetLifting :
    Localization.Lifting (perfectVerdierQuotient A D S) (perfectNullObjects A D S).trW
      ((supportedKernelPerfectFunctor A D B S U).obj
        (supportedKernelComposite A D E B S T U hD P Q) ⋙ perfectVerdierQuotient A B U)
      ((supportedKernelVerdierFunctor A D B S U).obj
        (supportedKernelComposite A D E B S T U hD P Q)) :=
  ⟨perfectKernelVerdierSquare A D B (supportedKernelComposite A D E B S T U hD P Q).obj
    (supportedKernelComposite A D E B S T U hD P Q).property.1 S U
    (supportedKernelComposite A D E B S T U hD P Q).property.2⟩

/-- 元の作用の合成比較を先に局所化して得る、実際の商関手の合成同型。 -/
def supportedKernelVerdierCompositionIso :
    (supportedKernelVerdierFunctor A D E S T).obj P ⋙
        (supportedKernelVerdierFunctor A E B T U).obj Q ≅
      (supportedKernelVerdierFunctor A D B S U).obj
        (supportedKernelComposite A D E B S T U hD P Q) :=
  Localization.liftNatIso (perfectVerdierQuotient A D S) (perfectNullObjects A D S).trW
    _ _ _ _ (isoWhiskerRight
      (supportedKernelPerfectCompositionIso A D E B S T U hD P Q) (perfectVerdierQuotient A B U))

/-- 元の Perf 対象上で、合成比較の降下は元の比較そのものを計算する。 -/
lemma supportedKernelVerdierCompositionIso_app (X : PerfectModuleCategory A D) :
    (supportedKernelVerdierCompositionIso A D E B S T U hD P Q).hom.app
        ((perfectVerdierQuotient A D S).obj X) =
      (supportedKernelVerdierCompositeFactors A D E B S T U P Q).hom.app X ≫
        (perfectVerdierQuotient A B U).map
          ((supportedKernelPerfectCompositionIso A D E B S T U hD P Q).hom.app X) ≫
        (perfectKernelVerdierSquare A D B
          (supportedKernelComposite A D E B S T U hD P Q).obj
          (supportedKernelComposite A D E B S T U hD P Q).property.1 S U
          (supportedKernelComposite A D E B S T U hD P Q).property.2).inv.app X :=
  Localization.liftNatTrans_app _ _ _ _ _ _ _ X

/-- 実際の Karoubi 延長の合成比較に、指定商上の kernel 合成同型を適用する。 -/
def supportedKernelCompletedCompositionIso :
    (supportedKernelCompletedFunctor A D E S T).obj P ⋙
        (supportedKernelCompletedFunctor A E B T U).obj Q ≅
      (supportedKernelCompletedFunctor A D B S U).obj
        (supportedKernelComposite A D E B S T U hD P Q) :=
  karoubiFunctorCompositionIso _ _ ≪≫
    (functorExtension₂ _ _).mapIso (supportedKernelVerdierCompositionIso A D E B S T U hD P Q)
end SerrePositivity.DifferentialGraded
end

end KernelCompositionDescent

/-! ## KernelCompositionComparison（旧 SerrePositivity/DifferentialGraded/Verdier/KernelCompositionComparison.lean） -/

/-! # kernel 合成と完備 tria 商・局所 perfect enhancement の比較 -/

@[expose] public section KernelCompositionComparison
universe u v w z

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents Morita

/-- 固定した比較同値による作用の輸送は、元の作用の合成同型を保つ。 -/
def conjugatedKernelCompositionIso
    {C₀ C₁ C₂ V₀ V₁ V₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* V₀] [Category* V₁] [Category* V₂]
    (e₀ : C₀ ≌ V₀) (e₁ : C₁ ≌ V₁) (e₂ : C₂ ≌ V₂)
    (P : V₀ ⥤ V₁) (Q : V₁ ⥤ V₂) (R : V₀ ⥤ V₂) (α : P ⋙ Q ≅ R) :
    (e₀.functor ⋙ P ⋙ e₁.inverse) ⋙ (e₁.functor ⋙ Q ⋙ e₂.inverse) ≅
      e₀.functor ⋙ R ⋙ e₂.inverse := by
  let β : e₁.inverse ⋙ (e₁.functor ⋙ (Q ⋙ e₂.inverse)) ≅ Q ⋙ e₂.inverse :=
    (associator _ _ _).symm ≪≫ isoWhiskerRight e₁.counitIso _ ≪≫ leftUnitor _
  exact associator _ _ _ ≪≫
    isoWhiskerLeft e₀.functor (associator _ _ _) ≪≫
    isoWhiskerLeft e₀.functor (isoWhiskerLeft P β) ≪≫
    isoWhiskerLeft e₀.functor (associator P Q e₂.inverse).symm ≪≫
    isoWhiskerLeft e₀.functor (isoWhiskerRight α e₂.inverse)

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (B : Type z) [DGCategory A B] [Small.{u} B]
  (S : Set D) (T : Set E) (U : Set B) (hD : localHomKFlat A D)
  (P : SupportedPerfectKernelCategory A D E S T)
  (Q : SupportedPerfectKernelCategory A E B T U)

namespace DGQuotient

/-- 完備 tria 商の実際の誘導作用にも、元の kernel 合成同型が降りる。 -/
def supportedKernelCompletedTriaCompositionIso :
    (supportedKernelCompletedTriaFunctor A D S E T).obj P ⋙
        (supportedKernelCompletedTriaFunctor A E T B U).obj Q ≅
      (supportedKernelCompletedTriaFunctor A D S B U).obj
        (supportedKernelComposite A D E B S T U hD P Q) :=
  conjugatedKernelCompositionIso
    (perfectCompletedToTriaQuotientEquivalence A D S).symm
    (perfectCompletedToTriaQuotientEquivalence A E T).symm
    (perfectCompletedToTriaQuotientEquivalence A B U).symm _ _ _
    (supportedKernelCompletedCompositionIso A D E B S T U hD P Q)

variable (hS : localKFlat A D S) (hT : localKFlat A E T) (hU : localKFlat A B U)

/-- 局所 perfect enhancement の H⁰ 作用の合成比較。局所条件は三つの商ごとに明示する。 -/
def supportedKernelLocalPerfectCompositionIso :
    (supportedKernelLocalPerfectFunctor A D S E T hS hT).obj P ⋙
        (supportedKernelLocalPerfectFunctor A E T B U hT hU).obj Q ≅
      (supportedKernelLocalPerfectFunctor A D S B U hS hU).obj
        (supportedKernelComposite A D E B S T U hD P Q) :=
  conjugatedKernelCompositionIso
    (localPerfectToPerfectVerdierEquivalence A D S hS)
    (localPerfectToPerfectVerdierEquivalence A E T hT)
    (localPerfectToPerfectVerdierEquivalence A B U hU) _ _ _
    (supportedKernelCompletedCompositionIso A D E B S T U hD P Q)
end DGQuotient
end SerrePositivity.DifferentialGraded
end

end KernelCompositionComparison

/-! ## KernelCompositionNaturality（旧 SerrePositivity/DifferentialGraded/Verdier/KernelCompositionNaturality.lean） -/

/-! # 降下した実際の kernel 合成比較の両 kernel 射に関する自然性 -/

@[expose] public section KernelCompositionNaturality
universe u v w z

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents Morita
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (B : Type z) [DGCategory A B] [Small.{u} B]
  (S : Set D) (T : Set E) (U : Set B) (hD : localHomKFlat A D)
  (P P' : SupportedPerfectKernelCategory A D E S T)
  (Q Q' : SupportedPerfectKernelCategory A E B T U) (f : P ⟶ P') (g : Q ⟶ Q')

/-- 許容 kernel の合成射は U16 の実際の主導来合成射。 -/
def supportedKernelCompositionMap :
    supportedKernelComposite A D E B S T U hD P Q ⟶
      supportedKernelComposite A D E B S T U hD P' Q' :=
  ObjectProperty.homMk (kernelComposeMap A D E B hD f.hom g.hom)

/-- 元の Perf 上に前合成した合成因子化は、kernel 射の水平合成に自然。 -/
lemma supportedKernelVerdierCompositeFactors_naturality :
    whiskerLeft (perfectVerdierQuotient A D S)
        (NatTrans.hcomp ((supportedKernelVerdierFunctor A D E S T).map f)
          ((supportedKernelVerdierFunctor A E B T U).map g)) ≫
        (supportedKernelVerdierCompositeFactors A D E B S T U P' Q').hom =
      (supportedKernelVerdierCompositeFactors A D E B S T U P Q).hom ≫
        whiskerRight (NatTrans.hcomp ((supportedKernelPerfectFunctor A D E S T).map f)
          ((supportedKernelPerfectFunctor A E B T U).map g)) (perfectVerdierQuotient A B U) :=
  horizontalComparison_naturality
    (perfectVerdierQuotient A D S) (perfectVerdierQuotient A E T) (perfectVerdierQuotient A B U)
    (perfectKernelVerdierSquare A D E P.obj P.property.1 S T P.property.2)
    (perfectKernelVerdierSquare A D E P'.obj P'.property.1 S T P'.property.2)
    (perfectKernelVerdierSquare A E B Q.obj Q.property.1 T U Q.property.2)
    (perfectKernelVerdierSquare A E B Q'.obj Q'.property.1 T U Q'.property.2)
    _ _ _ _ ((supportedKernelVerdierFactors A D E S T).hom.naturality f)
    ((supportedKernelVerdierFactors A E B T U).hom.naturality g)

/-- 実際に局所化した合成比較そのものは、両 kernel の任意の主導来射に自然。 -/
lemma supportedKernelVerdierCompositionIso_naturality :
    NatTrans.hcomp ((supportedKernelVerdierFunctor A D E S T).map f)
        ((supportedKernelVerdierFunctor A E B T U).map g) ≫
        (supportedKernelVerdierCompositionIso A D E B S T U hD P' Q').hom =
      (supportedKernelVerdierCompositionIso A D E B S T U hD P Q).hom ≫
        supportedKernelVerdierMap A D B S U
          (supportedKernelCompositionMap A D E B S T U hD P P' Q Q' f g) := by
  apply Localization.natTrans_ext (perfectVerdierQuotient A D S) (perfectNullObjects A D S).trW
  intro X
  simp only [NatTrans.comp_app, supportedKernelVerdierCompositionIso_app]
  let C := supportedKernelComposite A D E B S T U hD P Q
  let C' := supportedKernelComposite A D E B S T U hD P' Q'
  let fc := supportedKernelCompositionMap A D E B S T U hD P P' Q Q' f g
  have ha := NatTrans.congr_app
    (supportedKernelVerdierCompositeFactors_naturality A D E B S T U P P' Q Q' f g) X
  have hb := NatTrans.congr_app ((supportedKernelVerdierFactors A D B S U).hom.naturality fc) X
  have he := congrArg (perfectVerdierQuotient A B U).map
    (NatTrans.congr_app
      (supportedKernelPerfectCompositionIso_naturality A D E B S T U hD P Q P' Q' f g) X)
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at ha hb
  simp only [NatTrans.comp_app, CategoryTheory.Functor.map_comp] at he
  have h := transportedComparison_naturality
    ((supportedKernelVerdierCompositeFactors A D E B S T U P Q).app X)
    ((supportedKernelVerdierCompositeFactors A D E B S T U P' Q').app X)
    (((supportedKernelVerdierFactors A D B S U).app C).app X)
    (((supportedKernelVerdierFactors A D B S U).app C').app X)
    ((perfectVerdierQuotient A B U).mapIso
      ((supportedKernelPerfectCompositionIso A D E B S T U hD P Q).app X))
    ((perfectVerdierQuotient A B U).mapIso
      ((supportedKernelPerfectCompositionIso A D E B S T U hD P' Q').app X))
    _ _ _ _ ha hb he
  dsimp only [C, C', fc, supportedKernelVerdierFactors, supportedKernelVerdierFunctor] at h ⊢
  simpa only [Category.assoc, NatTrans.hcomp_app, NatIso.ofComponents.app,
    Iso.app_hom, Iso.app_inv, mapIso_hom, Functor.comp_map, Functor.comp_obj,
    Functor.whiskeringLeft_obj_map, Functor.whiskeringLeft_obj_obj, whiskerLeft_app] using h

section Karoubi
variable {C V W : Type*} [Category* C] [Category* V] [Category* W]
  {F F' : C ⥤ V} {G G' : V ⥤ W} (α : F ⟶ F') (β : G ⟶ G')

/-- Karoubi 延長の既存の合成比較も、両関手の自然変換に自然。 -/
lemma karoubiFunctorCompositionIso_naturality :
    NatTrans.hcomp ((functorExtension₂ C V).map α) ((functorExtension₂ V W).map β) ≫
        (karoubiFunctorCompositionIso F' G').hom =
      (karoubiFunctorCompositionIso F G).hom ≫
        (functorExtension₂ C W).map (NatTrans.hcomp α β) := by
  apply (whiskeringLeftObjToKaroubiFullyFaithful (C := C) (D := Karoubi W)).map_injective
  apply NatTrans.ext
  funext X
  apply Karoubi.hom_ext
  simp only [whiskeringLeft_obj_map, whiskerLeft_app,
    NatTrans.hcomp_app, karoubiFunctorCompositionIso, Iso.refl_hom,
    Karoubi.comp_f, functorExtension₂_obj_map_f, functorExtension₂_map_app_f,
    functorExtension₂_obj_obj_p, toKaroubi_obj_X, toKaroubi_obj_p,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  change (β.app (F.obj X) ≫ G'.map (𝟙 (F.obj X))) ≫ G'.map (α.app X) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
end Karoubi

/-- 完備化後の実際の合成比較も、両 kernel の任意の主導来射に自然。 -/
lemma supportedKernelCompletedCompositionIso_naturality :
    NatTrans.hcomp ((supportedKernelCompletedFunctor A D E S T).map f)
        ((supportedKernelCompletedFunctor A E B T U).map g) ≫
        (supportedKernelCompletedCompositionIso A D E B S T U hD P' Q').hom =
      (supportedKernelCompletedCompositionIso A D E B S T U hD P Q).hom ≫
        (supportedKernelCompletedFunctor A D B S U).map
          (supportedKernelCompositionMap A D E B S T U hD P P' Q Q' f g) := by
  simp only [supportedKernelCompletedCompositionIso, Iso.trans_hom, mapIso_hom]
  change NatTrans.hcomp
      ((functorExtension₂ _ _).map ((supportedKernelVerdierFunctor A D E S T).map f))
      ((functorExtension₂ _ _).map ((supportedKernelVerdierFunctor A E B T U).map g)) ≫ _ = _
  rw [← Category.assoc, karoubiFunctorCompositionIso_naturality, Category.assoc,
    ← CategoryTheory.Functor.map_comp, supportedKernelVerdierCompositionIso_naturality,
    CategoryTheory.Functor.map_comp]
  exact (Category.assoc _ _ _).symm
end SerrePositivity.DifferentialGraded
end

end KernelCompositionNaturality

/-! ## MoritaPairEquivalence（旧 SerrePositivity/DifferentialGraded/Verdier/MoritaPairEquivalence.lean） -/

/-! # 指定零部分圏を対応させる Morita 作用の商上の同値

実際の主 Perf 作用の同値性と、零部分圏の反映をそれぞれ明示する。
商上の同値や比較正方形の存在を入力にはしない。
-/

@[expose] public section MoritaPairEquivalence
universe u v w

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents Morita
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)
  (hK : kernelColumnsPerfect A D E K) (S : Set D) (T : Set E)
  (hST : ∀ d ∈ S, modulePerfectOver A E T ((kernelDerivedColumn A D E d).obj K))
  (hReflect : ∀ X : PerfectModuleCategory A D,
    perfectNullObjects A E T ((perfectDerivedKernelAction A D E K hK).obj X) →
      perfectNullObjects A D S X)

local instance moritaPairKernelShift : (perfectDerivedKernelAction A D E K hK).CommShift ℤ :=
  mainPerfectKernelActionCommShift A D E K hK
local instance moritaPairKernelTriangles :
    (perfectDerivedKernelAction A D E K hK).IsTriangulated :=
  mainPerfectKernelActionIsTriangulated A D E K hK

include hST hReflect in
lemma perfectKernelPairDenominators :
    (perfectNullObjects A D S).trW = (perfectNullObjects A E T).trW.inverseImage
      (perfectDerivedKernelAction A D E K hK) := by
  have hp : perfectNullObjects A D S = (perfectNullObjects A E T).inverseImage
      (perfectDerivedKernelAction A D E K hK) := by
    ext X
    exact ⟨perfectKernelNullObjects_image A D E K hK S T hST X, hReflect X⟩
  rw [hp]
  ext X Y f
  exact (perfectNullObjects A E T).inverseImage_trW_iff _ f

variable (hMorita : (perfectDerivedKernelAction A D E K hK).IsEquivalence)

include hReflect hMorita in
lemma perfectKernelPairVerdierIsEquivalence :
    (perfectKernelVerdierFunctor A D E K hK S T hST).IsEquivalence := by
  let Φ := LocalizerMorphism.ofEq (perfectKernelPairDenominators A D E K hK S T hST hReflect)
  have : Φ.functor.IsEquivalence := hMorita
  have : Φ.IsLocalizedEquivalence :=
    LocalizerMorphism.IsLocalizedEquivalence.of_equivalence Φ (by
      change (perfectNullObjects A E T).trW ≤
        (perfectNullObjects A D S).trW.map (perfectDerivedKernelAction A D E K hK)
      rw [perfectKernelPairDenominators A D E K hK S T hST hReflect,
        MorphismProperty.map_inverseImage_eq_of_isEquivalence])
  have : CatCommSq Φ.functor (perfectVerdierQuotient A D S) (perfectVerdierQuotient A E T)
      (perfectKernelVerdierFunctor A D E K hK S T hST) :=
    CatCommSq.mk (perfectKernelVerdierSquare A D E K hK S T hST).symm
  exact LocalizerMorphism.isEquivalence Φ
    (perfectVerdierQuotient A D S) (perfectVerdierQuotient A E T)
    (perfectKernelVerdierFunctor A D E K hK S T hST)

def perfectKernelPairVerdierEquivalence :
    PerfectVerdierQuotient A D S ≌ PerfectVerdierQuotient A E T :=
  letI := perfectKernelPairVerdierIsEquivalence A D E K hK S T hST hReflect hMorita
  (perfectKernelVerdierFunctor A D E K hK S T hST).asEquivalence

include hReflect hMorita in
lemma perfectKernelPairCompletedIsEquivalence :
    (perfectKernelCompletedVerdierFunctor A D E K hK S T hST).IsEquivalence :=
  (karoubiEquivalenceTransport
    (perfectKernelPairVerdierEquivalence A D E K hK S T hST hReflect hMorita)).isEquivalence_functor

namespace DGQuotient
variable (hD : localKFlat A D S) (hE : localKFlat A E T)

/-- 元の kernel の Morita 性と零部分圏の対応から、指定完備商上でも同値を得る。 -/
def mainKernelCompletedMoritaEquivalence :
    CompletedTriaQuotient A D S ≌ CompletedTriaQuotient A E T := by
  let := perfectKernelPairCompletedIsEquivalence A D E K hK S T hST hReflect hMorita
  have : (mainKernelCompletedQuotientFunctor A D S E K hK T hST).IsEquivalence := by
    dsimp [mainKernelCompletedQuotientFunctor]
    infer_instance
  exact (mainKernelCompletedQuotientFunctor A D S E K hK T hST).asEquivalence

/-- 実際に局所化した kernel 作用の、商 perfect enhancement の H⁰ 上の Morita 同値。 -/
def mainKernelLocalMoritaEquivalence :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ≌
      PerfectDGHomotopyCategoryOver A (QuotientObject E T) Set.univ := by
  let := perfectKernelPairCompletedIsEquivalence A D E K hK S T hST hReflect hMorita
  have : (mainKernelQuotientPerfectHomotopyFunctor A D S hD E K hK T hST hE).IsEquivalence := by
    dsimp [mainKernelQuotientPerfectHomotopyFunctor]
    infer_instance
  exact (mainKernelQuotientPerfectHomotopyFunctor A D S hD E K hK T hST hE).asEquivalence

instance mainKernelLocalMoritaFunctorCommShift :
    (mainKernelLocalMoritaEquivalence
      A D E K hK S T hST hReflect hMorita hD hE).functor.CommShift ℤ :=
  mainKernelQuotientPerfectHomotopyFunctorCommShift A D S hD E K hK T hST hE
instance mainKernelLocalMoritaInverseCommShift :
    (mainKernelLocalMoritaEquivalence
      A D E K hK S T hST hReflect hMorita hD hE).inverse.CommShift ℤ :=
  (mainKernelLocalMoritaEquivalence A D E K hK S T hST hReflect hMorita hD hE).commShiftInverse ℤ
instance mainKernelLocalMoritaCommShift :
    (mainKernelLocalMoritaEquivalence A D E K hK S T hST hReflect hMorita hD hE).CommShift ℤ :=
  (mainKernelLocalMoritaEquivalence
    A D E K hK S T hST hReflect hMorita hD hE).commShift_of_functor ℤ
instance mainKernelLocalMoritaIsTriangulated :
    (mainKernelLocalMoritaEquivalence A D E K hK S T hST hReflect hMorita hD hE).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _
    (mainKernelQuotientPerfectHomotopyFunctorIsTriangulated A D S hD E K hK T hST hE)

/-- Morita 同値の場合にも、既存の局所 perfect 比較と実際の誘導完備商関手が可換する。 -/
def mainKernelMoritaLocalPerfectSquare :
    (localPerfectQuotientEquivalence A D S hD).functor ⋙
        mainKernelCompletedQuotientFunctor A D S E K hK T hST ≅
      (mainKernelLocalMoritaEquivalence A D E K hK S T hST hReflect hMorita hD hE).functor ⋙
        (localPerfectQuotientEquivalence A E T hE).functor :=
  mainKernelLocalPerfectSquare A D S hD E K hK T hST hE

instance mainKernelMoritaLocalPerfectSquareCommShift :
    NatTrans.CommShift
      (mainKernelMoritaLocalPerfectSquare A D E K hK S T hST hReflect hMorita hD hE).hom ℤ :=
  mainKernelLocalPerfectSquareCommShift A D S hD E K hK T hST hE

def mainKernelMoritaLocalPerfectSquareTriangle :=
  Functor.mapTriangleIso
    (mainKernelMoritaLocalPerfectSquare A D E K hK S T hST hReflect hMorita hD hE)
end DGQuotient
end SerrePositivity.DifferentialGraded
end

end MoritaPairEquivalence

/-! ## GraphPairMorita（旧 SerrePositivity/DifferentialGraded/Verdier/GraphPairMorita.lean） -/

/-! # U16b の dg 擬同値から得る、指定局所 perfect 商上の Morita 同値

元の Perf 作用の同値性は U16b から証明する。
指定零部分圏の対応と局所 K-flat 条件は、それとは独立に明示する。
-/

@[expose] public section GraphPairMorita
universe u v w

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Morita
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma graphPairKernelColumnsPerfect : kernelColumnsPerfect A D E (kernelGraph A D E F) :=
  (kernelColumnsPerfect_iff_preservesPerfect A D E _).2
    (fun _ hX => quasiEquivalenceDerivedGraph_perfect A D E F hX)

/-- U16b の実際の graph 同型を用いた、元の主 Perf 作用の Morita 性。 -/
lemma graphPairKernelPerfectIsEquivalence (hF : QuasiEquivalence F) :
    (perfectDerivedKernelAction A D E (kernelGraph A D E F)
      (graphPairKernelColumnsPerfect A D E F)).IsEquivalence := by
  let : (quasiEquivalencePerfectExtension A D E F).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence A D E F hF).isEquivalence_functor
  exact Functor.isEquivalence_of_iso (quasiEquivalenceDerivedGraphOnPerfectIso A D E F).symm

variable (S : Set D) (T : Set E) (hST : ∀ d ∈ S, F.obj d ∈ T)

include hST in
lemma graphPairKernelSupportedColumns (d : D) (hd : d ∈ S) :
    modulePerfectOver A E T ((kernelDerivedColumn A D E d).obj (kernelGraph A D E F)) := by
  let e := (kernelDerivedColumnActionIso A D E (kernelGraph A D E F) d).symm ≪≫
    (quasiEquivalenceDerivedGraphIso A D E F).app
      ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))) ≪≫
    dgDerivedExtensionRepresentableIso A D E F d
  exact (modulePerfectOver A E T).prop_of_iso e.symm
    ((derivedFiniteCellOver A E T).le_retractClosure _
      ((moduleFiniteCellOver A E T).prop_map_obj (moduleToDerived A E)
        (moduleFiniteCellOver_representable A E (F.obj d) (hST d hd))))

namespace DGQuotient
variable (hF : QuasiEquivalence F)
  (hReflect : ∀ X : PerfectModuleCategory A D,
    perfectNullObjects A E T
        ((perfectDerivedKernelAction A D E (kernelGraph A D E F)
          (graphPairKernelColumnsPerfect A D E F)).obj X) → perfectNullObjects A D S X)
  (hD : localKFlat A D S) (hE : localKFlat A E T)

/-- 商の同値性を仮定せず、U16b と指定零部分圏の反映から得る局所 Morita 同値。 -/
def graphPairLocalMoritaEquivalence :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ≌
      PerfectDGHomotopyCategoryOver A (QuotientObject E T) Set.univ :=
  mainKernelLocalMoritaEquivalence A D E (kernelGraph A D E F)
    (graphPairKernelColumnsPerfect A D E F) S T
    (graphPairKernelSupportedColumns A D E F S T hST) hReflect
    (graphPairKernelPerfectIsEquivalence A D E F hF) hD hE

instance graphPairLocalMoritaFunctorCommShift :
    (graphPairLocalMoritaEquivalence A D E F S T hST hF hReflect hD hE).functor.CommShift ℤ :=
  mainKernelLocalMoritaFunctorCommShift _ _ _ _ _ _ _ _ _ _ _ _
instance graphPairLocalMoritaInverseCommShift :
    (graphPairLocalMoritaEquivalence A D E F S T hST hF hReflect hD hE).inverse.CommShift ℤ :=
  mainKernelLocalMoritaInverseCommShift _ _ _ _ _ _ _ _ _ _ _ _
instance graphPairLocalMoritaCommShift :
    (graphPairLocalMoritaEquivalence A D E F S T hST hF hReflect hD hE).CommShift ℤ :=
  mainKernelLocalMoritaCommShift _ _ _ _ _ _ _ _ _ _ _ _

instance graphPairLocalMoritaIsTriangulated :
    (graphPairLocalMoritaEquivalence A D E F S T hST hF hReflect hD hE).IsTriangulated :=
  mainKernelLocalMoritaIsTriangulated _ _ _ _ _ _ _ _ _ _ _ _

/-- U16b による Morita 同値も、元の作用から誘導した完備商関手と局所比較を可換にする。 -/
def graphPairLocalMoritaSquare :=
  mainKernelMoritaLocalPerfectSquare A D E (kernelGraph A D E F)
    (graphPairKernelColumnsPerfect A D E F) S T
    (graphPairKernelSupportedColumns A D E F S T hST) hReflect
    (graphPairKernelPerfectIsEquivalence A D E F hF) hD hE

instance graphPairLocalMoritaSquareCommShift :
    NatTrans.CommShift (graphPairLocalMoritaSquare A D E F S T hST hF hReflect hD hE).hom ℤ :=
  mainKernelMoritaLocalPerfectSquareCommShift _ _ _ _ _ _ _ _ _ _ _ _

def graphPairLocalMoritaSquareTriangle :=
  Functor.mapTriangleIso (graphPairLocalMoritaSquare A D E F S T hST hF hReflect hD hE)
end DGQuotient
end SerrePositivity.DifferentialGraded
end

end GraphPairMorita

/-! ## DerivedKernelGraphSquare（旧 SerrePositivity/DifferentialGraded/Verdier/DerivedKernelGraphSquare.lean） -/

/-! # 主導来 kernel 上の実際の graph 作用と局所 perfect 商比較

U16a の主局所化上の作用を使い、通常 bimodule の対象ごとの計算だけに留めない。
-/

@[expose] public section DerivedKernelGraphSquare
universe u v w

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory CategoryTheory.Functor Morita
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 主導来 graph kernel の実際の作用から、既存 graph 延長への関手自然同型。 -/
def derivedKernelGraphComparison :
    kernelDerivedTensor A D E (kernelGraph A D E F) ≅ dgDerivedExtension A D E F :=
  kernelDerivedTensorOnBimoduleIso A D E (BimoduleCategory.of A E D (functorGraph A D E F)) ≪≫
    eqToIso (kernelDerivedTensorOnBimodule_graph A D E F)

lemma derivedKernelGraph_perfect {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    modulePerfect A E ((kernelDerivedTensor A D E (kernelGraph A D E F)).obj X) :=
  (modulePerfect A E).prop_of_iso ((derivedKernelGraphComparison A D E F).app X).symm
    (dgDerivedExtension_perfect A D E F hX)

def derivedKernelGraphPerfectFunctor : PerfectModuleCategory A D ⥤ PerfectModuleCategory A E :=
  perfectFunctorRestriction A D E (kernelDerivedTensor A D E (kernelGraph A D E F))
    (fun _ hX => derivedKernelGraph_perfect A D E F hX)

def derivedKernelGraphPerfectComparison :
    derivedKernelGraphPerfectFunctor A D E F ≅ quasiEquivalencePerfectExtension A D E F :=
  perfectFunctorIso A D E _ _ (fun _ hX => derivedKernelGraph_perfect A D E F hX)
    (fun _ hX => dgDerivedExtension_perfect A D E F hX) (derivedKernelGraphComparison A D E F)

variable (S : Set D) (T : Set E) (hF : ∀ d ∈ S, F.obj d ∈ T)

/-- 主導来 graph kernel の作用そのものによる、全導来対象と射に自然な商正方形。 -/
def derivedKernelGraphQuotientSquare :
    kernelDerivedTensor A D (QuotientObject D S) (kernelGraph A D _ (inclusion A D S)) ⋙
        kernelDerivedTensor A (QuotientObject D S) (QuotientObject E T)
          (kernelGraph A _ _ (quotientDGFunctor A D E F S T hF)) ≅
      kernelDerivedTensor A D E (kernelGraph A D E F) ⋙
        kernelDerivedTensor A E (QuotientObject E T) (kernelGraph A E _ (inclusion A E T)) :=
  isoWhiskerRight (derivedKernelGraphComparison A D _ (inclusion A D S)) _ ≪≫
    isoWhiskerLeft _ (derivedKernelGraphComparison A _ _ (quotientDGFunctor A D E F S T hF)) ≪≫
    graphDerivedQuotientSquare A D E F S T hF ≪≫
    isoWhiskerLeft _ (derivedKernelGraphComparison A E _ (inclusion A E T)).symm ≪≫
    isoWhiskerRight (derivedKernelGraphComparison A D E F).symm _

def derivedKernelQuotientPerfectHomotopyFunctor :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ⥤
      PerfectDGHomotopyCategoryOver A (QuotientObject E T) Set.univ :=
  (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor ⋙
    derivedKernelGraphPerfectFunctor A _ _ (quotientDGFunctor A D E F S T hF) ⋙
      (perfectDGModuleHomotopyEquivalence A (QuotientObject E T) Set.univ).inverse

def derivedKernelQuotientPerfectHomotopyComparison :
    derivedKernelQuotientPerfectHomotopyFunctor A D E F S T hF ≅
      graphQuotientPerfectHomotopyFunctor A D E F S T hF :=
  isoWhiskerLeft _ (isoWhiskerRight
    (derivedKernelGraphPerfectComparison A _ _ (quotientDGFunctor A D E F S T hF)) _)

/-- 主導来 kernel の graph 作用と、指定された局所 perfect enhancement 比較の正方形。 -/
def derivedKernelLocalPerfectSquare (hD : localKFlat A D S) (hE : localKFlat A E T) :
    (localPerfectQuotientEquivalence A D S hD).functor ⋙
        graphCompletedVerdierFunctor A D E F S T hF ≅
      derivedKernelQuotientPerfectHomotopyFunctor A D E F S T hF ⋙
        (localPerfectQuotientEquivalence A E T hE).functor :=
  graphLocalPerfectSquare A D E F S T hF hD hE ≪≫
    isoWhiskerRight (derivedKernelQuotientPerfectHomotopyComparison A D E F S T hF).symm _
end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedKernelGraphSquare

/-! ## ConjugatedCompositionNaturality（旧 SerrePositivity/DifferentialGraded/Verdier/ConjugatedCompositionNaturality.lean） -/

/-! # 完備商・局所 perfect へ運んだ合成比較の自然性 -/

@[expose] public section ConjugatedCompositionNaturality
universe u v w z

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents Morita

section General
variable {C₀ C₁ C₂ V₀ V₁ V₂ : Type*}
  [Category* C₀] [Category* C₁] [Category* C₂]
  [Category* V₀] [Category* V₁] [Category* V₂]
  (e₀ : C₀ ≌ V₀) (e₁ : C₁ ≌ V₁) (e₂ : C₂ ≌ V₂)
  {P P' : V₀ ⥤ V₁} {Q Q' : V₁ ⥤ V₂} {R R' : V₀ ⥤ V₂}
  (α : P ⟶ P') (β : Q ⟶ Q') (γ : R ⟶ R') (e : P ⋙ Q ≅ R) (e' : P' ⋙ Q' ≅ R')

/-- 比較同値で運んだ合成同型は、元の合成同型の自然性を保つ。 -/
lemma conjugatedKernelCompositionIso_naturality
    (he : NatTrans.hcomp α β ≫ e'.hom = e.hom ≫ γ) :
    NatTrans.hcomp (whiskerLeft e₀.functor (whiskerRight α e₁.inverse))
        (whiskerLeft e₁.functor (whiskerRight β e₂.inverse)) ≫
        (conjugatedKernelCompositionIso e₀ e₁ e₂ P' Q' R' e').hom =
      (conjugatedKernelCompositionIso e₀ e₁ e₂ P Q R e).hom ≫
        whiskerLeft e₀.functor (whiskerRight γ e₂.inverse) := by
  apply NatTrans.ext
  funext X
  have hc := e₁.counitIso.hom.naturality (α.app (e₀.functor.obj X))
  simp only [Functor.comp_map, Functor.id_map] at hc
  have hb := β.naturality (e₁.counitIso.hom.app (P.obj (e₀.functor.obj X)))
  have hh := NatTrans.congr_app he (e₀.functor.obj X)
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, Category.assoc] at hh
  simp only [conjugatedKernelCompositionIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app, associator_inv_app, associator_hom_app,
    leftUnitor_hom_app, NatTrans.hcomp_app, Functor.comp_map, Functor.comp_obj,
    Functor.id_obj, Category.id_comp, Category.assoc]
  simp only [← CategoryTheory.Functor.map_comp]
  apply congrArg e₂.inverse.map
  rw [← Q'.map_comp_assoc, hc, Q'.map_comp, Category.assoc,
    ← reassoc_of% hb, hh]
end General

namespace DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (B : Type z) [DGCategory A B] [Small.{u} B]
  (S : Set D) (T : Set E) (U : Set B) (hD : localHomKFlat A D)
  (P P' : SupportedPerfectKernelCategory A D E S T)
  (Q Q' : SupportedPerfectKernelCategory A E B T U) (f : P ⟶ P') (g : Q ⟶ Q')

lemma supportedKernelCompletedTriaCompositionIso_naturality :
    NatTrans.hcomp ((supportedKernelCompletedTriaFunctor A D S E T).map f)
        ((supportedKernelCompletedTriaFunctor A E T B U).map g) ≫
        (supportedKernelCompletedTriaCompositionIso A D E B S T U hD P' Q').hom =
      (supportedKernelCompletedTriaCompositionIso A D E B S T U hD P Q).hom ≫
        (supportedKernelCompletedTriaFunctor A D S B U).map
          (supportedKernelCompositionMap A D E B S T U hD P P' Q Q' f g) :=
  conjugatedKernelCompositionIso_naturality
    (perfectCompletedToTriaQuotientEquivalence A D S).symm
    (perfectCompletedToTriaQuotientEquivalence A E T).symm
    (perfectCompletedToTriaQuotientEquivalence A B U).symm _ _ _ _ _
    (supportedKernelCompletedCompositionIso_naturality A D E B S T U hD P P' Q Q' f g)

variable (hS : localKFlat A D S) (hT : localKFlat A E T) (hU : localKFlat A B U)

lemma supportedKernelLocalPerfectCompositionIso_naturality :
    NatTrans.hcomp ((supportedKernelLocalPerfectFunctor A D S E T hS hT).map f)
        ((supportedKernelLocalPerfectFunctor A E T B U hT hU).map g) ≫
        (supportedKernelLocalPerfectCompositionIso A D E B S T U hD P' Q' hS hT hU).hom =
      (supportedKernelLocalPerfectCompositionIso A D E B S T U hD P Q hS hT hU).hom ≫
        (supportedKernelLocalPerfectFunctor A D S B U hS hU).map
          (supportedKernelCompositionMap A D E B S T U hD P P' Q Q' f g) :=
  conjugatedKernelCompositionIso_naturality
    (localPerfectToPerfectVerdierEquivalence A D S hS)
    (localPerfectToPerfectVerdierEquivalence A E T hT)
    (localPerfectToPerfectVerdierEquivalence A B U hU) _ _ _ _ _
    (supportedKernelCompletedCompositionIso_naturality A D E B S T U hD P P' Q Q' f g)
end DGQuotient
end SerrePositivity.DifferentialGraded
end

end ConjugatedCompositionNaturality
