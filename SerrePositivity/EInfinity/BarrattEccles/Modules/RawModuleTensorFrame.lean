module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleHomQuillen
public import SerrePositivity.EInfinity.Modules.TensorSimplices
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexReedy
public import SerrePositivity.EInfinity.AlexanderWhitney.SimplexCounitContraction
public import SerrePositivity.EInfinity.ProjectiveCofibrantUnit
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor

/-!
# 同じ半自由 BE 加群の正規化単体 source frame

概要：M10 の元の半自由加群に、同じ全単体テンソルの実 frame 条件を証明する。
方針：N01 の実モデル、同じ tensor/Hom 随伴、既存の正規化単体を使う。
規約：HA §1.3.4、モデル構造を仮定せず、全標的の通常 Hom を保持する。
使われ方：元の dg Hom と通常 DK 局所化の写像空間の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite MonoidalCategory HomologicalComplex HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
variable (A : Type u) [CommRing A]

/-- 概要：元の半自由加群の係数テンソル関手は実モデルで左 Quillen。
方針：同じ実随伴と検証済みの Hom の右 Quillen 条件を使う。
規約：HA §1.3.4、実モデル。使われ方：同じ正規化単体の frame 移送。 -/
lemma strictRawModuleSemifree_tensor_isLeftQuillen (X : (operad A).Algebra)
    (P : strictRawModuleCategory A X)
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P) :
    letI := projectiveModelCategory A
    letI := strictRawModuleModelCategory A X
    SerrePositivity.Quillen.IsLeftQuillen
      (tensorModuleFunctor (ForgetEnrichment.to (Complex A) P)) := by
  let := projectiveModelCategory A
  let := strictRawModuleModelCategory A X
  have := strictRawModuleSemifree_hom_isRightQuillen A X P hP
  exact SerrePositivity.Quillen.isLeftQuillen_of_isRightQuillen
    (moduleTensorHomAdjunction A (dgAlgebraCategory A ((assocForget A).obj X)) P)

/-- 概要：同じ半自由加群の全単体テンソルは実 Reedy cofibrant。
方針：既存の正規化単体の Reedy cofibrancy を同じ左随伴で送る。
規約：HA §1.3.4、同じ全族。使われ方：モデル frame Hom の Kan 性。 -/
lemma strictRawModuleTensorFrame_reedyCofibrant (X : (operad A).Algebra)
    (P : strictRawModuleCategory A X)
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P) :
    letI := strictRawModuleModelCategory A X
    reedyLeft simplex (cofibrations (strictRawModuleCategory A X))
      (initial.to ((moduleTensorSimplicesFunctor A
        (dgAlgebraCategory A ((assocForget A).obj X))).obj P)) := by
  let := projectiveModelCategory A
  let := strictRawModuleModelCategory A X
  have := strictRawModuleSemifree_tensor_isLeftQuillen A X P hP
  have :=
    (moduleTensorHomAdjunction A (dgAlgebraCategory A ((assocForget A).obj X)) P).isLeftAdjoint
  exact leftQuillen_frame_reedyCofibrant
    (tensorModuleFunctor (ForgetEnrichment.to (Complex A) P))
    (SSet.stdSimplex ⋙ normalizedFunctor A) (ComplexLimits.normalizedSimplex_reedyCofibrant A)

/-- 概要：同じ半自由 source frame の全ての作用素は元の弱同値。
方針：元の AW 余単位の実収縮と Brown の補題で同じ左 Quillen 関手を送る。
規約：HA §1.3.4、全ての面・退化。使われ方：homotopically constant 条件。 -/
lemma strictRawModuleTensorFrame_homotopicallyConstant (X : (operad A).Algebra)
    (P : strictRawModuleCategory A X)
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P)
    {n m : SimplexCategory} (f : n ⟶ m) :
    letI := strictRawModuleModelCategory A X
    weakEquivalences (strictRawModuleCategory A X)
      (((moduleTensorSimplicesFunctor A
        (dgAlgebraCategory A ((assocForget A).obj X))).obj P).map f) := by
  let := projectiveModelCategory A
  let := strictRawModuleModelCategory A X
  have := strictRawModuleSemifree_tensor_isLeftQuillen A X P hP
  have hc : ∀ {n m : SimplexCategory} (g : n ⟶ m),
      weakEquivalences (Complex A) ((SSet.stdSimplex ⋙ normalizedFunctor A).map g) := by
    intro n m g
    change QuasiIso (AlexanderWhitney.cochainMap A (SSet.stdSimplex.map g))
    let εn := AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n)
    let εm := AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj m)
    have hn : QuasiIso εn := (AlexanderWhitney.cochainCounitStdSimplexHomotopyEquiv A n).quasiIso_hom
    have hm : QuasiIso εm := (AlexanderWhitney.cochainCounitStdSimplexHomotopyEquiv A m).quasiIso_hom
    have : QuasiIso (AlexanderWhitney.cochainMap A (SSet.stdSimplex.map g) ≫ εm) := by
      change QuasiIso (AlexanderWhitney.cochainMap A (SSet.stdSimplex.map g) ≫
        AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj m))
      rw [AlexanderWhitney.cochainCounit_natural]
      exact hn
    exact quasiIso_of_comp_right _ εm
  exact leftQuillen_frame_homotopicallyConstant
    (tensorModuleFunctor (ForgetEnrichment.to (Complex A) P))
    (SSet.stdSimplex ⋙ normalizedFunctor A) (ComplexLimits.normalizedSimplex_reedyCofibrant A) hc f

/-- 概要：同じ半自由加群への指定 augmentation は各次数で元の擬同型。
方針：同じ AW 余単位を左 Quillen 関手で送り、同じ左単位同型と合成する。
規約：HA §1.3.4、元の射自身。使われ方：共通 frame の底の比較。 -/
lemma strictRawModuleTensorFrame_augmentation_weak (X : (operad A).Algebra)
    (P : strictRawModuleCategory A X)
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P)
    (n : SimplexCategory) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))
      ((moduleTensorSimplicesAugmentation A
        (dgAlgebraCategory A ((assocForget A).obj X)) P).app n) := by
  let := projectiveModelCategory A
  let := strictRawModuleModelCategory A X
  let D := dgAlgebraCategory A ((assocForget A).obj X)
  let L := tensorModuleFunctor (ForgetEnrichment.to (Complex A) P)
  have := strictRawModuleSemifree_tensor_isLeftQuillen A X P hP
  have : IsCofibrant (AlexanderWhitney.cochains A (SSet.stdSimplex.obj n)) :=
    cosimplicialFrame_isCofibrant_obj (SSet.stdSimplex ⋙ normalizedFunctor A)
      (ComplexLimits.normalizedSimplex_reedyCofibrant A) n
  have hu : Cofibration (0 : (HomologicalComplex.zero : Complex A) ⟶ 𝟙_ (Complex A)) :=
    ⟨projectiveCofibrant_unit⟩
  have : IsCofibrant (𝟙_ (Complex A)) :=
    (isCofibrant_iff_of_isInitial _ HomologicalComplex.isZero_zero.isInitial).mpr hu
  let ε := AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n)
  have : WeakEquivalence ε :=
    ⟨(AlexanderWhitney.cochainCounitStdSimplexHomotopyEquiv A n).quasiIso_hom⟩
  have hε : WeakEquivalence (L.map ε) :=
    SerrePositivity.Quillen.map_weakEquivalence_of_cofibrant L ε
  have hc := (weakEquivalences (strictRawModuleCategory A X)).comp_mem (L.map ε)
    (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) P)).hom
    ((HomotopicalAlgebra.weakEquivalence_iff _).mp hε)
    ((weakEquivalences (strictRawModuleCategory A X)).of_isIso _)
  exact (strictRawModuleModelCategory_weakEquivalences A X) ▸ hc

/-- 概要：同じ半自由 source frame から任意の元の加群への全単体 Hom は Kan。
方針：実 Reedy 条件・全作用素の弱同値性・N01 の全対象の fibrancy を使う。
規約：HA §1.3.4、単体集合のモデルを仮定しない。使われ方：元の写像空間比較。 -/
lemma strictRawModuleTensorHom_kanComplex (X : (operad A).Algebra)
    (P N : strictRawModuleCategory A X)
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P) :
    SSet.KanComplex
      ((cosimplicialHom
        ((moduleTensorSimplicesFunctor A
          (dgAlgebraCategory A ((assocForget A).obj X))).obj P)).obj N) := by
  let := strictRawModuleModelCategory A X
  have := strictRawModuleModelCategory_allFibrant A X N
  exact cosimplicialHom_kanComplex _ (strictRawModuleTensorFrame_reedyCofibrant A X P hP)
    (strictRawModuleTensorFrame_homotopicallyConstant A X P hP) N

end SerrePositivity.EInfinity.BarrattEccles
