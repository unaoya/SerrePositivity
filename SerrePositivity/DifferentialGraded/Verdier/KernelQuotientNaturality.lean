module
public import SerrePositivity.DifferentialGraded.Verdier.KernelLocalPerfectSquare

/-! # 許容する主導来 kernel の全射に自然な指定 Verdier 作用

元の Perf 作用の kernel 関手性を、実際の指定局所化へ降ろす。
-/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
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
