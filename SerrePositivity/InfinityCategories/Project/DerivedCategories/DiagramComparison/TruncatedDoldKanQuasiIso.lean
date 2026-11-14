module
public import SerrePositivity.EInfinity.ComplexLimits.DoldKanPinchedChainNaturality
public import SerrePositivity.EInfinity.ComplexLimits.TruncatedDoldKanFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.PinchedChainMapQuasiIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Reflection

/-!
概要：非有界複体の準同型を、同じ smart 切断・Γ 写像の単体的ホモトピー同値へ移す。
方針：実 pinched Hom の準同型不変性と既存 Γ 比較の自然性を使い、単位 Hom で一般複体へ戻す。
規約：指定した元の鎖写像の Γ 像を保ち、別の同値で代用しない。
使われ方：HA 1.2.4、G10 の Hom–Tot 鎖比較から全単体の比較への移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type u} [CommRing A]

/-- 実 Hom 準同型の同じ Γ 像は単体的ホモトピー同値。 -/
theorem doldKanHomSpaceChainMap_quasiIso_equivalence
    {D E : Type v} [DGCategory A D] [DGCategory A E]
    {x y : D} {x' y' : E}
    (f : homObject A D x y ⟶ homObject A E x' y') [QuasiIso f] :
    IsSimplicialHomotopyEquivalence (doldKanHomSpaceChainMap f) := by
  have h := (qCatEquivalenceOfIso (doldKanHomPinchedIso (R := A) x y)).isQCatEquivalence.comp
    (pinchedHomChainMap_quasiIso_equivalence f).isQCatEquivalence
  change IsQCatEquivalence ((doldKanHomPinchedIso (R := A) x y).hom ≫
    pinchedHomChainMap f) at h
  rw [← doldKanHomPinchedIso_chainMap] at h
  have hu := (qCatEquivalenceOfIso (doldKanHomPinchedIso (R := A) x' y')).isQCatEquivalence.cancel_right h
  exact ((isQCatEquivalence_ulift_iff_of_kan (doldKanHomSpaceChainMap f)).mp hu).isSimplicialHomotopyEquivalence

/-- 任意複体の同じ切断 Γ を単位 Hom の Γ と比較する指定同型。 -/
def truncatedDoldKanUnitIso (K : Complex A) :
    (truncatedDoldKanFunctor A).obj K ≅ doldKanHomSpace (R := A) (D := Complex A)
      (𝟙_ (Complex A)) K :=
  (truncatedDoldKanFunctor A).mapIso (complexUnitHomIso K)

open SSet.modelCategoryQuillen in
/-- 任意非有界複体の smart 切断 Γ は Kan 複体である。 -/
instance truncatedDoldKanFunctor_kan (K : Complex A) :
    SSet.KanComplex ((truncatedDoldKanFunctor A).obj K) :=
  HomotopicalAlgebra.isFibrant_of_fibration (truncatedDoldKanUnitIso K).hom

/-- 元の非有界準同型の同じ smart 切断 Γ 写像は単体的ホモトピー同値。 -/
theorem truncatedDoldKanFunctor_quasiIso_equivalence {K L : Complex A}
    (f : K ⟶ L) [QuasiIso f] :
    IsSimplicialHomotopyEquivalence ((truncatedDoldKanFunctor A).map f) := by
  let T := truncatedDoldKanFunctor A
  let := complexUnitHomPostcompose_quasiIso f
  have hp := (doldKanHomSpaceChainMap_quasiIso_equivalence
    (D := Complex A) (E := Complex A) (x := 𝟙_ (Complex A)) (y := K)
    (x' := 𝟙_ (Complex A)) (y' := L) (homPostcompose (𝟙_ (Complex A)) f)).isQCatEquivalence
  have h := (qCatEquivalenceOfIso (truncatedDoldKanUnitIso K)).isQCatEquivalence.comp hp
  change IsQCatEquivalence (T.map (complexUnitHomIso K).hom ≫
    T.map (homPostcompose (𝟙_ (Complex A)) f)) at h
  rw [← T.map_comp, complexUnitHomIso_naturality, T.map_comp] at h
  exact ((qCatEquivalenceOfIso (truncatedDoldKanUnitIso L)).isQCatEquivalence.cancel_right h).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
