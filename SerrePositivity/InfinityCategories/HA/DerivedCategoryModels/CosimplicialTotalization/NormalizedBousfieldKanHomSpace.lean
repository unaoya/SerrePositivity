module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanConeRepresentative
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.TruncatedDoldKanQuasiIso

/-!
概要：元の Tot の実 Dold–Kan Hom 空間と、正規化 BK Hom 複体の Γ を同値で結ぶ。
方針：同じ Hom–Tot・正規化 BK 比較を鎖ホモトピー同値として保持し、その Γ 像を取る。
規約：全単体の実射を固定する。重み付き切断空間との比較は別工程。
使われ方：HA 1.2.4、G10 の native Hom 比較の同値性への入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 同じ Hom–Tot 比較から実正規化 BK Hom への指定鎖ホモトピー同値。 -/
def homToNormalizedBousfieldKanHomotopyEquiv (P : Complex A)
    (X : CosimplicialObject (Complex A)) :
    HomotopyEquiv (homComplex A P ((productTotalFunctor A).obj X))
      (normalizedBousfieldKanHom ((homDiagramFunctor P).obj X)) :=
  (HomotopyEquiv.ofIso ((homTotalNatIso P).app X)).trans
    (normalizedBousfieldKanHomHomotopyEquiv ((homDiagramFunctor P).obj X))

/-- 鎖ホモトピー同値の前向き射は元の指定比較そのもの。 -/
theorem homToNormalizedBousfieldKanHomotopyEquiv_hom (P : Complex A)
    (X : CosimplicialObject (Complex A)) :
    (homToNormalizedBousfieldKanHomotopyEquiv P X).hom = homToNormalizedBousfieldKan P X := rfl

instance homToNormalizedBousfieldKan_quasiIso (P : Complex A)
    (X : CosimplicialObject (Complex A)) : QuasiIso (homToNormalizedBousfieldKan P X) :=
  inferInstanceAs (QuasiIso (homToNormalizedBousfieldKanHomotopyEquiv P X).hom)

/-- 元の Tot の実 Hom 空間から正規化 BK Hom の Γ への指定全単体比較。 -/
def normalizedBousfieldKanHomSpaceComparison (P : Complex A)
    (X : CosimplicialObject (Complex A)) :
    doldKanHomSpace (R := A) (D := Complex A) P ((productTotalFunctor A).obj X) ⟶
      (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj (normalizedBousfieldKanHom ((homDiagramFunctor P).obj X)) :=
  (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map (homToNormalizedBousfieldKan P X)

/-- 同じ指定全単体比較は単体的ホモトピー同値である。 -/
theorem normalizedBousfieldKanHomSpaceComparison_equivalence (P : Complex A)
    (X : CosimplicialObject (Complex A)) :
    IsSimplicialHomotopyEquivalence (normalizedBousfieldKanHomSpaceComparison P X) :=
  truncatedDoldKanFunctor_quasiIso_equivalence (homToNormalizedBousfieldKan P X)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
