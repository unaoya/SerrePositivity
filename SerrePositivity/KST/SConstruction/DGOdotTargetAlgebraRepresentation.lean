module
public import SerrePositivity.KST.SConstruction.DGOdotTargetConeRepresentationNaturality
public import SerrePositivity.KST.SConstruction.DGOdotTargetAlgebra
public import SerrePositivity.KST.SConstruction.DGOdotAlgebraRealization
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomPrecomposition

/-! # 元の ⊙ 比較代数射と評価した商 cone の表現照合
概要：元の比較代数射の実 Yoneda 作用を、同じ商 cone 評価と全 Hom 自然に比較する。
方針：代数化の同じ基礎鎖写像を厳密に回収し、元の商 End 比較を前合成する。
規約：元の代数射・全次数成分を保持。使われ方：実 Perf 延長比較の元の代表上の界面。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.source d)
local notation "CRaw" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.left d)
local notation "DRaw" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.right d)
local notation "E" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.corner d)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.top d)
local notation "gRaw" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.side d)
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.lower d)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.upper d)
local notation "CL" => DGSmallPerfectArrowTarget R (A) (CRaw) (L)
local notation "DR" => DGSmallPerfectArrowTarget R (A) (DRaw) (gRaw)
local notation "pS" => dgSmallPerfectSquareLeftMap R (A) (CRaw) (DRaw) (E) (L) (gRaw) (p) (q)
local notation "qS" => dgSmallPerfectSquareRightMap R (A) (CRaw) (DRaw) (E) (L) (gRaw) (p) (q)
local notation "I" => dgOdotQuotientInput R d

local notation "Y" => dgSmallPerfectEnvelopeYoneda R (DRaw) (DGSmallPerfectBase R (A))
  (dgSmallPerfectEnvelopeExtensionFamily R (A) (DRaw) Empty
    (dgSmallPerfectBaseFamily R (A)) (gRaw))
local notation "M" => dgHomGluingBimodule R (CL) (DR) (DGOdotCorner R d) (pS) (qS)
local notation "zc" => dgSmallPerfectArrowTargetZero R (A) (CRaw) (L)
local notation "hc" => dgSmallPerfectArrowTargetZero_isZero R (A) (CRaw) (L)
local notation "b" => dgOdotInputRightPoint R d

local notation "J" => dgSmallPerfectSquareCornerInclusion R (A) (CRaw) (DRaw) (E)
  (L) (gRaw) (p) (q)

local notation "B" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (dgOdotAlgebra R d)

/-- 元の ⊙ 比較代数射が、元の終域の自由代表に作用する同じ実関手。 -/
def dgOdotTargetAlgebraRepresentation : DGFunctor R (B) (RightModule R (E)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotTargetMap R d)).comp (dgYoneda R (E))

/-- 元の ⊙ から元の指定商 End を経由して評価した、同じ実 cone 作用。 -/
def dgOdotConeAlgebraRepresentation : DGFunctor R (B) (RightModule R (E)) :=
  (dgOdotAlgebraToEnd R d).comp (dgOdotRealizedConeRepresentation R d)

/-- 元の代数化の Hom 回収は、同じ自由代表作用の厳密な関手等号を与える。 -/
lemma dgOdotTargetAlgebraRepresentation_eq :
    (dgOdotAlgebraToEnd R d).comp (dgOdotRawTargetRepresentation R d) =
      dgOdotTargetAlgebraRepresentation R d := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgOdotAlgebraToEnd R d).comp (dgOdotRawTargetRepresentation R d))
    (G := dgOdotTargetAlgebraRepresentation R d) (fun _ => rfl)
  intro x y
  change (𝟙 _ ≫ (((dgOdotTargetCornerEndMap R d).map
    EndomorphismObject.point EndomorphismObject.point ≫ 𝟙 _) ≫
      yonedaHom R (E) ((q).obj (b)) ((q).obj (b)))) ≫ eqToHom (by rfl) =
    (dgOdotTargetMap R d).hom ≫ yonedaHom R (E) ((q).obj (b)) ((q).obj (b))
  rw [eqToHom_refl, Category.comp_id, Category.id_comp, Category.comp_id,
    dgOdotTargetMap_hom]
  rfl

/-- 元の比較代数射の自由代表作用への、同じ実 cone からの全次数自然比較。 -/
def dgOdotTargetAlgebraRepresentationComparison :
    DGFunctorParamTrans R (B) (RightModule R (E)) (𝟙_ (Complex R))
      (dgOdotConeAlgebraRepresentation R d) (dgOdotTargetAlgebraRepresentation R d) := by
  rw [← dgOdotTargetAlgebraRepresentation_eq]
  exact dgFunctorParamPre R (DGOdotQuotientEnd R d) (RightModule R (E)) (B)
    (dgOdotAlgebraToEnd R d) (dgOdotRawConeRepresentationComparison R d)

/-- 同じ元の三段 cone 同型の逆から得る、元の代数表現への全次数逆比較。 -/
def dgOdotTargetAlgebraRepresentationInverseComparison :
    DGFunctorParamTrans R (B) (RightModule R (E)) (𝟙_ (Complex R))
      (dgOdotTargetAlgebraRepresentation R d) (dgOdotConeAlgebraRepresentation R d) := by
  rw [← dgOdotTargetAlgebraRepresentation_eq]
  exact dgFunctorParamPre R (DGOdotQuotientEnd R d) (RightModule R (E)) (B)
    (dgOdotAlgebraToEnd R d) (dgOdotRawConeRepresentationInverseComparison R d)

/-- 同じ実代数表現の閉零自然同型。元の商 cone の同型を同じ前合成で使う。 -/
def dgOdotTargetAlgebraRepresentationClosedIso :
    (dgOdotConeAlgebraRepresentation R d).onClosed ≅
      (dgOdotTargetAlgebraRepresentation R d).onClosed :=
  EnrichedFunctor.forgetComp (dgOdotAlgebraToEnd R d) (dgOdotRealizedConeRepresentation R d) ≪≫
    Functor.isoWhiskerLeft (dgOdotAlgebraToEnd R d).onClosed
      (dgOdotRawConeRepresentationClosedIso R d) ≪≫
        (EnrichedFunctor.forgetComp (dgOdotAlgebraToEnd R d)
          (dgOdotRawTargetRepresentation R d)).symm ≪≫
            eqToIso (congrArg (fun F => F.onClosed) (dgOdotTargetAlgebraRepresentation_eq R d))

end SerrePositivity.KST.SConstruction
