module

public import SerrePositivity.EInfinity.Modules.TensorAugmentationCurry
public import SerrePositivity.EInfinity.ComplexLimits.ExtendedTruncationZeroMono
public import SerrePositivity.EInfinity.ComplexLimits.StandardDoldKanZeroRawEvaluation
public import SerrePositivity.EInfinity.ComplexLimits.StandardDoldKanPinchedComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedClosedStandardConstant

/-!
# 元の加群 augmentation 像と同じ恒等辺

概要：M10 の元の実 Γ 零次像を同じ標準恒等頂点へ同定する。
方針：同じ単射な直接評価で元の恒等閉 cochain を比較し、同じ pinched 同型で送る。
規約：HA 1.3.1.13、元の Γ・標準同型・単位辺を保持する。
使われ方：元の全普遍族の augmentation 像の同じ恒等辺への較正。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory Opposite SSet
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：元の恒等閉射の同じ標準実 Γ 零次像。
方針：元の標準定数単体へ同じ標準/Γ 同型を適用する。
規約：HA 1.3.1.13、同じ恒等射。使われ方：元の augmentation 像の比較点。 -/
def moduleIdentityDoldKanVertex (P : ModuleCategory A D) :
    (((moduleDoldKanHomBifunctor A D).obj (op P)).obj P) _⦋0⦌ :=
  (standardDoldKanModuleIso (R := A) (D := RightModule A D)
    (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) P)).hom.app (op ⦋0⦌)
    (standardConstant (closedHomEquiv A (RightModule A D) P P (𝟙 P)) 0)

/-- 概要：同じ標準恒等 Γ 頂点の直接評価は元の恒等閉 cochain。
方針：既存の同じ標準同型の零次直接評価と定数の一点成分式を使う。
規約：HA 1.3.1.13、同じ実評価。使われ方：元の二頂点の単射による照合。 -/
lemma moduleIdentityDoldKanVertex_raw (P : ModuleCategory A D) :
    truncationExtendedZeroInclusion A ComplexShape.embeddingDownNat
      embeddingDownNat_eq_upIntLE_zero rfl
      (moduleHom A D (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) P))
      ((gammaDegreeZeroIso (connectiveHomComplex (R := A) (D := RightModule A D)
        (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) P))).hom
          (moduleIdentityDoldKanVertex A D P)) =
    (closedHomEquiv A (RightModule A D) P P (𝟙 P)).val := by
  have h0 := standardDoldKanModuleIso_zero_raw (R := A) (D := RightModule A D)
    (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) P)
    (standardConstant (closedHomEquiv A (RightModule A D) P P (𝟙 P)) 0)
  have h := standardConstant_singleton (closedHomEquiv A (RightModule A D) P P (𝟙 P)) (0 : Fin 1)
  have h' : (standardConstant (closedHomEquiv A (RightModule A D) P P (𝟙 P)) 0).val.component
      Finset.univ 0 Finset.univ_nonempty (by simp) =
    (closedHomEquiv A (RightModule A D) P P (𝟙 P)).val := by
    simpa only [show (Finset.univ : Finset (Fin 1)) = {0} from by decide] using h
  exact h0.trans h'

/-- 概要：元の augmentation Γ 零次像は同じ標準恒等頂点。
方針：同じ直接評価の単射性と二つの元の評価式を使う。
規約：HA 1.3.1.13、同じ Γ。使われ方：元の恒等 pinched 辺の回収。 -/
lemma moduleTensorAugmentation_gamma_zero_eq (P : ModuleCategory A D) :
    moduleTensorAugmentationDoldKanVertex A D P = moduleIdentityDoldKanVertex A D P := by
  apply gammaDegreeZero_raw_injective A
    (moduleHom A D (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) P))
  exact (moduleTensorAugmentation_gamma_zero_raw A D P).trans
    (moduleIdentityDoldKanVertex_raw A D P).symm

/-- 概要：同じ標準恒等 Γ 頂点は元の恒等閉 pinched 辺へ移る。
方針：同じ標準/Γ/pinched 比較を元の定数零単体で評価する。
規約：HA 1.3.1.13、元の閉射。使われ方：同じ augmentation 像の指定恒等辺。 -/
lemma moduleIdentityDoldKanVertex_pinched (P : ModuleCategory A D) :
    (moduleDoldKanPinchedIso A D P P).hom.app (op ⦋0⦌) (ULift.up (moduleIdentityDoldKanVertex A D P)) =
      pinchedClosedVertex A (RightModule A D) (𝟙 P) := by
  let s : StandardSimplex A (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) P) 0 :=
    standardConstant (closedHomEquiv A (RightModule A D) P P (𝟙 P)) 0
  have h := congrArg (fun f : SSet.uliftFunctor.{max (u + 1) v, u}.obj
      (standardHomSpace (R := A) (D := RightModule A D)
        (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) P)) ⟶
      PinchedHom.pinchedHom A (RightModule A D)
        (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) P) =>
      f.app (op ⦋0⦌) (ULift.up s))
    (standardDoldKanPinchedComparison (R := A) (D := RightModule A D)
      (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) P))
  change (moduleDoldKanPinchedIso A D P P).hom.app (op ⦋0⦌)
      (ULift.up (moduleIdentityDoldKanVertex A D P)) =
    pinchedClosedStandardSimplex A (RightModule A D) (𝟙 P) 0 at h
  exact h.trans (pinchedClosedStandardSimplex_zero A (RightModule A D) _)

/-- 概要：元の augmentation の pinched 像は同じ元の恒等閉辺。
方針：同じ Γ 零次像の等式を同じ座標同型で送る。
規約：HA 1.3.1.13、指定恒等射。使われ方：元の全 augmentation 三角形の単位。 -/
lemma moduleTensorAugmentationVertex_identity (P : ModuleCategory A D) :
    moduleTensorAugmentationPinchedVertex A D P =
      pinchedClosedVertex A (RightModule A D) (𝟙 P) := by
  exact (congrArg (fun z => (moduleDoldKanPinchedIso A D P P).hom.app (op ⦋0⦌) (ULift.up z))
    (moduleTensorAugmentation_gamma_zero_eq A D P)).trans
      (moduleIdentityDoldKanVertex_pinched A D P)

/-- 概要：元の全普遍 pinched 族の augmentation 像は同じ恒等辺の定値族。
方針：同じ全定値化と元の零次恒等辺の等式を合成する。
規約：HA 1.3.1.13、全次数。使われ方：同じ全 cone の単位三角形。 -/
lemma moduleTensorUniversalPinchedSimplex_augmentation_identity (P : ModuleCategory A D)
    (n : SimplexCategory) :
    moduleTensorUniversalPinchedSimplex A D P n ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) P
        ((moduleTensorSimplicesAugmentation A D P).app n)) =
    SSet.const (pinchedClosedVertex A (RightModule A D) (𝟙 P)) := by
  exact (moduleTensorUniversalPinchedSimplex_augmentation A D P n).trans
    (congrArg (fun z => SSet.const (X := SSet.uliftFunctor.{max (u + 1) v, u}.obj
      (SSet.stdSimplex.obj n)) z) (moduleTensorAugmentationVertex_identity A D P))

end SerrePositivity.EInfinity.Modules
