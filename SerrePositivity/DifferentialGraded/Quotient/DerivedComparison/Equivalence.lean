module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.LayerTriangles
public import SerrePositivity.DifferentialGraded.Verdier.Derived

public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.LocalFlatness
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.ColimitCones

public import Mathlib.CategoryTheory.Localization.Triangulated
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations
public import SerrePositivity.DifferentialGraded.Perfect.Compact.FiniteGeneration

/-!
# Quotient.DerivedComparison.Equivalence

## 概要
生成・有限 roof からの完全忠実性、Verdier 比較同値と perfect enhancementをまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## DerivedComparisonAdjointUnit（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonAdjointUnit.lean） -/

/-! # 代表加群上の導来随伴と実際の比較写像の整合性

普通の加群の射影置換のみを使い、Hom 比較の正規化を固定する。
-/

@[expose] public section DerivedComparisonAdjointUnit
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 標準の射影置換の増強を延長して得る、導来延長から underived 延長への比較。 -/
def derivedExtensionUnderivedMap (M : ModuleCategory A D) :
    (dgDerivedExtension A D E F).obj ((moduleToDerived A D).obj M) ⟶
      (moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj M) :=
  (dgDerivedExtensionResolutionComputation A D E F
      (moduleCanonicalProjectiveResolution A D M)).hom ≫
    (moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map
      (moduleCanonicalProjectiveResolution A D M).π)

/-- 実際の加群射への転置は、導来比較と可換である。 -/
lemma derivedExtensionUnderivedMap_homEquiv (M : ModuleCategory A D)
    (N : ModuleCategory A E) (s : (dgModuleExtension A D E F).onClosed.obj M ⟶ N) :
    dgDerivedExtensionHomEquiv A D E F ((moduleToDerived A D).obj M)
      ((moduleToDerived A E).obj N)
      (derivedExtensionUnderivedMap A D E F M ≫ (moduleToDerived A E).map s) =
    (moduleToDerived A D).map
      ((dgModuleEnrichedRestrictionAdjunction A D E F).homEquiv M N s) ≫
        (dgDerivedRestrictionComputation A D E F N).inv := by
  change dgDerivedExtensionHomEquivOnModules A D E F M N _ = _
  rw [dgDerivedExtensionHomEquivOnModules_apply]
  unfold derivedExtensionUnderivedMap
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← CategoryTheory.Functor.map_comp, dgProjectiveDerivedExtensionHomEquiv_map,
    Adjunction.homEquiv_naturality_left, CategoryTheory.Functor.map_comp]
  simp only [← Category.assoc]
  have hi := (moduleDerivedIso A D (moduleCanonicalProjectiveResolution A D M).π
    (moduleCanonicalProjectiveResolution A D M).quasiIso).inv_hom_id
  change (moduleDerivedIso A D (moduleCanonicalProjectiveResolution A D M).π
    (moduleCanonicalProjectiveResolution A D M).quasiIso).inv ≫
      (moduleToDerived A D).map (moduleCanonicalProjectiveResolution A D M).π = 𝟙 _ at hi
  rw [hi, Category.id_comp]

/-- ホモトピー射影的な加群では、この比較は同型である。 -/
lemma derivedExtensionUnderivedMap_isIso (M : ModuleCategory A D)
    (hM : moduleHomotopicallyProjective A D M) :
    IsIso (derivedExtensionUnderivedMap A D E F M) := by
  have h := moduleToDerived_inverts A E _
    (dgModuleExtension_projective_quasiIso A D E F
      (moduleCanonicalProjectiveResolution A D M).projective hM
      (moduleCanonicalProjectiveResolution A D M).π
      (moduleCanonicalProjectiveResolution A D M).quasiIso)
  let := h
  unfold derivedExtensionUnderivedMap
  infer_instance

/-- 随伴の転置が元の Hom 包含となるように正規化した代表加群の延長同型。 -/
def derivedExtensionRepresentableUnitIso (z : D) :
    (dgDerivedExtension A D E F).obj
        ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A z))) ≅
      (moduleToDerived A E).obj
        (ForgetEnrichment.of (Complex A) (representable A (F.obj z))) := by
  let M := ForgetEnrichment.of (Complex A) (representable A z)
  let := derivedExtensionUnderivedMap_isIso A D E F M
    (representable_homotopicallyProjective A D z)
  exact asIso (derivedExtensionUnderivedMap A D E F M) ≪≫
    (moduleToDerived A E).mapIso (dgModuleExtensionRepresentableIso A D E F z)

/-- 上の代表同型を転置すると、既存の代表加群比較写像を得る。 -/
lemma derivedExtensionRepresentableUnitIso_homEquiv (z : D) :
    dgDerivedExtensionHomEquiv A D E F
      ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A z)))
      ((moduleToDerived A E).obj
        (ForgetEnrichment.of (Complex A) (representable A (F.obj z))))
      (derivedExtensionRepresentableUnitIso A D E F z).hom =
    (moduleToDerived A D).map (representableRestrictionMap A D E F z) ≫
      (dgDerivedRestrictionComputation A D E F
        (ForgetEnrichment.of (Complex A) (representable A (F.obj z)))).inv := by
  change dgDerivedExtensionHomEquiv A D E F _ _
    (derivedExtensionUnderivedMap A D E F _ ≫
      (moduleToDerived A E).map (dgModuleExtensionRepresentableIso A D E F z).hom) = _
  rw [derivedExtensionUnderivedMap_homEquiv, Adjunction.homEquiv_unit,
    dgModuleEnrichedRestrictionAdjunction_unit]
  rw [dgModuleRestriction_map]
  exact congrArg (fun t => (moduleToDerived A D).map t ≫
    (dgDerivedRestrictionComputation A D E F
      (ForgetEnrichment.of (Complex A) (representable A (F.obj z)))).inv)
    (functorExtensionUnit_representable A D E F z)


end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonAdjointUnit

/-! ## DerivedComparisonFreeGeneration（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonFreeGeneration.lean） -/

/-! # 自由右加群の導来像の局所生成

一対象環からの導来延長と代表加群による帰納法を接続する。
-/

@[expose] public section DerivedComparisonFreeGeneration
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- b の代表加群を含む localizing な性質は、一対象環からの全導来延長の像を含む。 -/
lemma pointDerivedExtension_mem
    (P : ObjectProperty (DerivedModuleCategory A D)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms]
    (hcoprod : ∀ (I : Type u) (G : I → DerivedModuleCategory A D),
      (∀ i, P (G i)) → P (∐ G)) (b : D)
    (hb : P ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A b))))
    (X : DerivedModuleCategory A PUnit.{1}) :
    P ((dgDerivedExtension A PUnit.{1} D (pointDGFunctor A D b)).obj X) := by
  let := dgDerivedExtensionCommShift A PUnit.{1} D (pointDGFunctor A D b)
  let := dgDerivedExtensionIsTriangulated A PUnit.{1} D (pointDGFunctor A D b)
  let := (dgDerivedExtensionRestrictionAdjunction A PUnit.{1} D
    (pointDGFunctor A D b)).isLeftAdjoint
  apply moduleDerived_functor_generatorInduction A PUnit.{1} D
    (dgDerivedExtension A PUnit.{1} D (pointDGFunctor A D b)) P hcoprod
    (fun _ => inferInstance) _ X
  intro x
  cases x
  exact P.prop_of_iso (dgDerivedExtensionRepresentableIso A PUnit.{1} D
    (pointDGFunctor A D b) PUnit.unit).symm hb

/-- K-flat 係数の自由加群へ compact 対象から向かう射は S 上の有限 cell を経由する。 -/
lemma freeAtKFlat_finiteCellFactorTarget (S : Set D) (b : D) (hb : b ∈ S)
    (K : Complex A) (hK : complexKFlat A K) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj ((freeAt b).obj K)) := by
  have hrep : moduleFiniteCellFactorTarget A D S
      ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A b))) :=
    moduleFiniteCellFactorTarget_of_finiteCell A D
      ((moduleFiniteCellOver A D S).prop_map_obj (moduleToDerived A D)
        (moduleFiniteCellOver_representable A D b hb))
  exact (moduleFiniteCellFactorTarget A D S).prop_of_iso (derivedFreeAtKFlatIso A D b K hK)
    (pointDerivedExtension_mem A D (moduleFiniteCellFactorTarget A D S)
      (fun _ G hG => moduleFiniteCellFactorTarget_coproduct A D G hG) b hrep
      ((moduleToDerived A PUnit.{1}).obj (ForgetEnrichment.of (Complex A) (ringModule A K))))

/-- 一対象環の通常の射影置換を評価して、任意の複体の K-flat 置換を得る。 -/
lemma exists_coefficientKFlat_resolution (K : Complex A) :
    ∃ (P : Complex A) (q : P ⟶ K), complexKFlat A P ∧ QuasiIso q := by
  let M := ForgetEnrichment.of (Complex A) (ringModule A K)
  let P := moduleCanonicalProjectiveResolution A PUnit.{1} M
  refine ⟨(moduleEvaluation A PUnit.{1} PUnit.unit).obj P.obj,
    (moduleEvaluation A PUnit.{1} PUnit.unit).map P.π, ?_, P.quasiIso PUnit.unit⟩
  intro L hL
  have hp := moduleHomotopicallyProjective_relativeKFlat A PUnit.{1} P.projective
    (ringLeftModule A L) (fun _ => hL)
  exact cochainAcyclic_of_iso hp
    (BalancedTensor.ringIso A (ForgetEnrichment.to (Complex A) P.obj) (ringLeftModule A L))

/-- 代表加群の値が K-flat なら、自由加群関手は係数の擬同型を保つ。 -/
lemma freeAt_quasiIso_of_homKFlat (b : D)
    (hb : ∀ x : D, complexKFlat A (homObject A D x b))
    {K L : Complex A} (q : K ⟶ L) [QuasiIso q] :
    moduleQuasiIso A D ((freeAt b).map q) := by
  intro x
  change QuasiIso ((moduleEvaluation A D x).map (tensorModuleMap q (representable A b)))
  rw [tensorModuleMap_eval]
  exact complexKFlat_quasiIso_left A (hb x) q

/-- 入る側の局所 K-flat 性の下では、係数複体を任意に取れる。 -/
lemma freeAt_finiteCellFactorTarget_into (S : Set D) (h : homIntoKFlat A D S)
    (b : S) (K : Complex A) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj ((freeAt b.val).obj K)) := by
  obtain ⟨P, q, hP, hq⟩ := exists_coefficientKFlat_resolution A K
  have := hq
  exact (moduleFiniteCellFactorTarget A D S).prop_of_iso
    (moduleDerivedIso A D ((freeAt b.val).map q)
      (freeAt_quasiIso_of_homKFlat A D b.val (fun x => h x b) q))
    (freeAtKFlat_finiteCellFactorTarget A D S b.val b.property P hP)

/-- 片側局所 K-flat 仮定の下で、全ての正の path 項は S による有限因子分解性を持つ。 -/
lemma positivePath_finiteCellFactorTarget (S : Set D) (h : localKFlat A D S)
    (b : S) (w : Word S) (z : D) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (pathModule A D (b :: w) z))) := by
  apply (moduleFiniteCellFactorTarget A D S).prop_of_iso
    ((moduleToDerived A D).mapIso (pathModuleFreeIso A D b w z)).symm
  rcases h with h | h
  · exact freeAt_finiteCellFactorTarget_into A D S h b (pathSuffixWeight A D w b z)
  · exact freeAtKFlat_finiteCellFactorTarget A D S b.val b.property
      (pathSuffixWeight A D w b z) (pathSuffixWeight_kFlat A D h w b z)

/-- M9 の次数零 flat Hom からも、同じ正の path の有限因子分解性を供給できる。 -/
lemma positivePath_finiteCellFactorTarget_of_flat_zero
    (hz : ∀ (x y : D) (i : ℤ), i ≠ 0 → IsZero ((homObject A D x y).X i))
    (hf : ∀ x y : D, Module.Flat A ((homObject A D x y).X 0))
    (S : Set D) (b : S) (w : Word S) (z : D) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (pathModule A D (b :: w) z))) :=
  positivePath_finiteCellFactorTarget A D S
    (Or.inl (allHomKFlat_into A D (allHomKFlat_of_flat_zero A D hz hf) S)) b w z

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonFreeGeneration

/-! ## DerivedComparisonLayerGeneration（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonLayerGeneration.lean） -/

/-! # 局所 K-flat 仮定による長さ層と有限長比較 cone の生成

正の path 項の生成性を、実際の加群直和の導来像と長さ filtration の各層へ運ぶ。
-/

@[expose] public section DerivedComparisonLayerGeneration
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleCoproduct_finiteCellFactorTarget (S : Set D) {I : Type w} [Small.{u} I]
    (M : I → ModuleCategory A D)
    (hM : ∀ i, moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj (M i))) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj (∐ M)) :=
  (moduleFiniteCellFactorTarget A D S).prop_of_iso (moduleDerivedCoproductIso A D M)
    (moduleFiniteCellFactorTarget_coproduct_small A D _ hM)

/-- 同じ有限因子分解性は、厳密な加群図式の逐次余極限でも保たれる。 -/
lemma moduleSequentialColimit_finiteCellFactorTarget (S : Set D)
    (F : ℕ ⥤ ModuleCategory A D)
    (hF : ∀ n, moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj (F.obj n)))
    (s : Cocone F) (hs : IsColimit s) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj s.pt) := by
  let R := sequentialCoproductFamily.{u} F
  have hR : moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj (∐ R)) :=
    moduleCoproduct_finiteCellFactorTarget A D S R (fun i => hF i.down)
  have hc : moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj
      (moduleCone A D (sequentialCoproductMap.{u} F))) :=
    (moduleFiniteCellFactorTarget A D S).ext_of_isTriangulatedClosed₃ _
      (moduleDerivedConeTriangle_distinguished A D (sequentialCoproductMap.{u} F)) hR hR
  exact (moduleFiniteCellFactorTarget A D S).prop_of_iso
    (moduleDerivedIso A D (moduleSequentialConeDesc A D F s)
      (moduleSequentialConeDesc_quasiIso A D F s hs)) hc

lemma nonemptyPath_finiteCellFactorTarget (S : Set D) (h : localKFlat A D S)
    (w : Word S) (hw : w ≠ []) (z : D) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (pathModule A D w z))) := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons b w => exact positivePath_finiteCellFactorTarget A D S h b w z

/-- 全ての正の固定長層の導来像は、S に関する有限因子分解性を持つ。 -/
lemma lengthLayerModule_finiteCellFactorTarget (S : Set D) (h : localKFlat A D S)
    (z : D) (n : ℕ) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj
      (selectedPathModule A D S (fun w => w.length = n + 1) z)) := by
  apply moduleCoproduct_finiteCellFactorTarget A D S
    (fun w : LengthWord S (n + 1) => ForgetEnrichment.of (Complex A) (pathModule A D w.val z))
  intro w
  apply nonemptyPath_finiteCellFactorTarget A D S h w.val _ z
  intro hw
  have hh := w.property
  rw [hw, List.length_nil] at hh
  omega

lemma lengthLayerCone_finiteCellFactorTarget (S : Set D) (h : localKFlat A D S)
    (z : D) (n : ℕ) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj
      (moduleCone A D (lengthModuleTransition A D S z (Nat.le_succ n)))) :=
  (moduleFiniteCellFactorTarget A D S).prop_of_iso (lengthLayerDerivedConeIso A D S z n).symm
    (lengthLayerModule_finiteCellFactorTarget A D S h z n)

lemma lengthModuleTransition_trW (S : Set D) (h : localKFlat A D S) (z : D) (n : ℕ) :
    (moduleFiniteCellFactorTarget A D S).trW
      ((moduleToDerived A D).map (lengthModuleTransition A D S z (Nat.le_succ n))) :=
  ((moduleFiniteCellFactorTarget A D S).trW_iff_of_distinguished
    (lengthLayerDerivedTriangle A D S z n) (lengthLayerDerivedTriangle_distinguished A D S z n)).mpr
      (lengthLayerModule_finiteCellFactorTarget A D S h z n)

/-- 零段階から任意の有限長段階への比較は、同じ三角部分圏に関する分母となる。 -/
lemma lengthZeroToStage_trW (S : Set D) (h : localKFlat A D S) (z : D) (n : ℕ) :
    (moduleFiniteCellFactorTarget A D S).trW
      ((moduleToDerived A D).map (lengthModuleTransition A D S z (Nat.zero_le n))) := by
  let P := moduleFiniteCellFactorTarget A D S
  let F := lengthModuleDiagram A D S z ⋙ moduleToDerived A D
  have hs (k : ℕ) : P.trW (F.map (homOfLE (Nat.le_succ k))) :=
    lengthModuleTransition_trW A D S h z k
  change P.trW (F.map (homOfLE (Nat.zero_le n)))
  induction n with
  | zero =>
    have he : homOfLE (Nat.zero_le 0) = 𝟙 (0 : ℕ) := Subsingleton.elim _ _
    rw [he, CategoryTheory.Functor.map_id]
    exact P.trW.id_mem _
  | succ n ih =>
    have he : homOfLE (Nat.zero_le n) ≫ homOfLE (Nat.le_succ n) =
        homOfLE (Nat.zero_le (n + 1)) := Subsingleton.elim _ _
    have ht := P.trW.comp_mem _ _ ih (hs n)
    rw [← CategoryTheory.Functor.map_comp, he] at ht
    exact ht

lemma lengthZeroToStageCone_finiteCellFactorTarget (S : Set D) (h : localKFlat A D S)
    (z : D) (n : ℕ) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj
      (moduleCone A D (lengthModuleTransition A D S z (Nat.zero_le n)))) :=
  ((moduleFiniteCellFactorTarget A D S).trW_iff_of_distinguished
    (moduleDerivedConeTriangle A D (lengthModuleTransition A D S z (Nat.zero_le n)))
    (moduleDerivedConeTriangle_distinguished A D
      (lengthModuleTransition A D S z (Nat.zero_le n)))).mp
        (lengthZeroToStage_trW A D S h z n)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonLayerGeneration

/-! ## DerivedComparisonUnitCone（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonUnitCone.lean） -/

/-! # 商への代表加群比較の cone の局所生成

有限長比較 cone の厳密な余極限から、実際の比較射の cone へ移す。
-/

@[expose] public section DerivedComparisonUnitCone
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 零段階から商全体への比較 cone の導来像は、S による有限因子分解性を持つ。 -/
lemma lengthInclusionCone_finiteCellFactorTarget (S : Set D) (h : localKFlat A D S) (z : D) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj
      (moduleCone A D (lengthModuleInclusion A D S z 0))) := by
  exact moduleSequentialColimit_finiteCellFactorTarget A D S
    (lengthComparisonConeDiagram A D S z)
    (fun n => lengthZeroToStageCone_finiteCellFactorTarget A D S h z n)
    (lengthComparisonConeCocone A D S z) (lengthComparisonConeCocone_isColimit A D S z)

/-- 始点の同型で結ばれる二つの射の cone は同型。 -/
def moduleConeSourceIso {M N T : ModuleCategory A D}
    (f : M ⟶ T) (g : N ⟶ T) (e : M ≅ N) (h : e.hom ≫ g = f) :
    moduleCone A D f ≅ moduleCone A D g :=
  (moduleConeFunctor A D).mapIso (X := Arrow.mk f) (Y := Arrow.mk g)
    (Arrow.isoMk' f g e (Iso.refl T) (by simpa using h))

/-- 元の代表加群を始点とする比較 cone と零段階を始点とする比較 cone の同型。 -/
def quotientRepresentableComparisonConeIso (S : Set D) (z : D) :
    moduleCone A D
        (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z) ≅
      moduleCone A D (lengthModuleInclusion A D S z 0) :=
  moduleConeSourceIso A D
    (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z)
    (lengthModuleInclusion A D S z 0) (lengthZeroModuleIso A D S z)
    (lengthZeroModuleMap_inclusion A D S z)

/-- 局所 K-flat 版の、商への実際の代表加群比較の cone の有限因子分解性。 -/
lemma quotientRepresentableComparisonCone_finiteCellFactorTarget
    (S : Set D) (h : localKFlat A D S) (z : D) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj
      (moduleCone A D
        (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z))) :=
  (moduleFiniteCellFactorTarget A D S).prop_of_iso
    ((moduleToDerived A D).mapIso (quotientRepresentableComparisonConeIso A D S z)).symm
    (lengthInclusionCone_finiteCellFactorTarget A D S h z)

lemma quotientRepresentableComparison_trW (S : Set D) (h : localKFlat A D S) (z : D) :
    (moduleFiniteCellFactorTarget A D S).trW ((moduleToDerived A D).map
      (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z)) :=
  ((moduleFiniteCellFactorTarget A D S).trW_iff_of_distinguished
    (moduleDerivedConeTriangle A D
      (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z))
    (moduleDerivedConeTriangle_distinguished A D
      (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z))).mpr
        (quotientRepresentableComparisonCone_finiteCellFactorTarget A D S h z)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonUnitCone

/-! ## DerivedComparisonFiniteRoof（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonFiniteRoof.lean） -/

/-! # 比較 cone の有限因子分解性から Verdier 分母を作る

有限 cell の始域から局所化対象への射を、有限 cell の分母を使って持ち上げる。
-/

@[expose] public section DerivedComparisonFiniteRoof
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma derivedFiniteCell_subset_univ (S : Set D) :
    derivedFiniteCellOver A D S ≤ derivedFiniteCellOver A D Set.univ :=
  (derivedFiniteCellOver_le_iff_generators A D
    (derivedFiniteCellOver A D Set.univ) S).2 (fun x _ =>
      (moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToDerived A D)
        (moduleFiniteCell_representable A D x))

/-- 指定有限 cell を経由する射は、その cone も指定有限 cell である分母で消せる。 -/
lemma finiteCellFactor_exists_denominator (S : Set D)
    {X Y : DerivedModuleCategory A D} (hX : derivedFiniteCellOver A D Set.univ X)
    (f : X ⟶ Y) (hf : ModuleFiniteCellFactor A D S f) :
    ∃ (E : DerivedModuleCategory A D), derivedFiniteCellOver A D Set.univ E ∧
      ∃ s : E ⟶ X, (derivedFiniteCellOver A D S).trW s ∧ s ≫ f = 0 := by
  obtain ⟨P, hP, a, b, hab⟩ := hf
  obtain ⟨E, s, δ, hT⟩ := distinguished_cocone_triangle₁ a
  have hE := (derivedFiniteCellOver A D Set.univ).ext_of_isTriangulatedClosed₁
    _ hT hX (derivedFiniteCell_subset_univ A D S P hP)
  refine ⟨E, hE, s, ObjectProperty.trW.mk _ hT hP, ?_⟩
  have hs0 : s ≫ a = 0 := comp_distTriang_mor_zero₁₂ _ hT
  rw [← hab, ← Category.assoc, hs0, zero_comp]

/-- cone が有限因子分解性を持つ比較三角形に対する、有限 cell 始域の射の roof 表示。 -/
lemma finiteCellRoof_of_cone_factorTarget (S : Set D)
    (T : Triangle (DerivedModuleCategory A D))
    (hT : T ∈ distTriang (DerivedModuleCategory A D))
    (hC : moduleFiniteCellFactorTarget A D S T.obj₃)
    {X : DerivedModuleCategory A D} (hX : derivedFiniteCellOver A D Set.univ X)
    (f : X ⟶ T.obj₂) :
    ∃ (E : DerivedModuleCategory A D), derivedFiniteCellOver A D Set.univ E ∧
      ∃ (s : E ⟶ X) (g : E ⟶ T.obj₁),
        (derivedFiniteCellOver A D S).trW s ∧ g ≫ T.mor₁ = s ≫ f := by
  have hc : moduleCompact A D X := modulePerfectOver_compact A D
    ((derivedFiniteCellOver A D Set.univ).le_retractClosure X hX)
  obtain ⟨E, hE, s, hs, hz⟩ := finiteCellFactor_exists_denominator A D S hX
    (f ≫ T.mor₂) (hC X hc (f ≫ T.mor₂))
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T hT (s ≫ f)
    (by rw [Category.assoc]; exact hz)
  exact ⟨E, hE, s, g, hs, hg.symm⟩

/-- 比較後に零になる射は、比較 cone の逆 shift を経由して有限 cell に因子分解する。 -/
lemma finiteCellFactor_of_comparison_zero (S : Set D)
    (T : Triangle (DerivedModuleCategory A D))
    (hT : T ∈ distTriang (DerivedModuleCategory A D))
    (hC : moduleFiniteCellFactorTarget A D S T.obj₃)
    {X : DerivedModuleCategory A D} (hX : moduleCompact A D X)
    (f : X ⟶ T.obj₁) (hf : f ≫ T.mor₁ = 0) :
    ModuleFiniteCellFactor A D S f := by
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T.invRotate
    (inv_rot_of_distTriang _ hT) f hf
  rw [hg]
  exact (moduleFiniteCellFactorTarget_shift A D hC (-1) X hX g).postcompose A D _

/-- 比較後に零になる射は、指定有限 cell の cone を持つ分母で既に零になる。 -/
lemma comparison_zero_exists_finiteCell_denominator (S : Set D)
    (T : Triangle (DerivedModuleCategory A D))
    (hT : T ∈ distTriang (DerivedModuleCategory A D))
    (hC : moduleFiniteCellFactorTarget A D S T.obj₃)
    {X : DerivedModuleCategory A D} (hX : derivedFiniteCellOver A D Set.univ X)
    (f : X ⟶ T.obj₁) (hf : f ≫ T.mor₁ = 0) :
    ∃ (E : DerivedModuleCategory A D), derivedFiniteCellOver A D Set.univ E ∧
      ∃ s : E ⟶ X, (derivedFiniteCellOver A D S).trW s ∧ s ≫ f = 0 :=
  finiteCellFactor_exists_denominator A D S hX f
    (finiteCellFactor_of_comparison_zero A D S T hT hC
      (modulePerfectOver_compact A D
        ((derivedFiniteCellOver A D Set.univ).le_retractClosure X hX)) f hf)

/-- 商の制限代表加群への任意の有限 cell 始域の射は、Verdier 分母の後で持ち上がる。 -/
lemma quotientRepresentable_exists_finiteCellRoof (S : Set D)
    (h : localKFlat A D S) (z : D)
    {X : DerivedModuleCategory A D} (hX : derivedFiniteCellOver A D Set.univ X)
    (f : X ⟶ (moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z))) :
    ∃ (E : DerivedModuleCategory A D), derivedFiniteCellOver A D Set.univ E ∧
      ∃ (s : E ⟶ X)
        (g : E ⟶ (moduleToDerived A D).obj
          (ForgetEnrichment.of (Complex A) (representable A z))),
        (derivedFiniteCellOver A D S).trW s ∧
        g ≫ (moduleToDerived A D).map
          (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z) = s ≫ f :=
  finiteCellRoof_of_cone_factorTarget A D S _
    (moduleDerivedConeTriangle_distinguished A D
      (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z))
    (quotientRepresentableComparisonCone_finiteCellFactorTarget A D S h z) hX f

/-- 同じ roof を、U17a の tria(D) とその指定 Verdier 分母の中で表す。 -/
lemma quotientRepresentable_exists_triaRoof (S : Set D)
    (h : localKFlat A D S) (z : D) (X : TriaCategory A D)
    (f : (triaInclusion A D).obj X ⟶ (moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z))) :
    ∃ (E : TriaCategory A D) (s : E ⟶ X) (g : E ⟶ triaRepresentable A D z),
      (triaImage A D S).trW s ∧
        (triaInclusion A D).map g ≫ (moduleToDerived A D).map
          (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z) =
            (triaInclusion A D).map s ≫ f := by
  obtain ⟨E, hE, s, g, hs, hg⟩ :=
    quotientRepresentable_exists_finiteCellRoof A D S h z X.property f
  let E' : TriaCategory A D := ⟨E, hE⟩
  let s' : E' ⟶ X := ObjectProperty.homMk s
  let g' : E' ⟶ triaRepresentable A D z := ObjectProperty.homMk g
  refine ⟨E', s', g', ?_, hg⟩
  exact ((derivedFiniteCellOver A D S).inverseImage_trW_iff (triaInclusion A D) s').2 hs

/-- U17a の局所化で、代表加群比較の核に入る射は零になる。 -/
lemma triaQuotient_map_eq_zero_of_representableComparison (S : Set D)
    (h : localKFlat A D S) (z : D) (X : TriaCategory A D)
    (f : X ⟶ triaRepresentable A D z)
    (hf : (triaInclusion A D).map f ≫ (moduleToDerived A D).map
      (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z) = 0) :
    (triaQuotient A D S).map f = 0 := by
  obtain ⟨E, hE, s, hs, hz⟩ := comparison_zero_exists_finiteCell_denominator A D S
    (moduleDerivedConeTriangle A D
      (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z))
    (moduleDerivedConeTriangle_distinguished A D
      (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z))
    (quotientRepresentableComparisonCone_finiteCellFactorTarget A D S h z)
    X.property ((triaInclusion A D).map f) hf
  let E' : TriaCategory A D := ⟨E, hE⟩
  let s' : E' ⟶ X := ObjectProperty.homMk s
  have hs' : (triaImage A D S).trW s' :=
    ((derivedFiniteCellOver A D S).inverseImage_trW_iff (triaInclusion A D) s').2 hs
  have hz' : s' ≫ f = 0 := by
    apply (triaInclusion A D).map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero]
    change s ≫ (triaInclusion A D).map f = 0
    exact hz
  have : IsIso ((triaQuotient A D S).map s') :=
    Localization.inverts (triaQuotient A D S) (triaImage A D S).trW s' hs'
  apply (cancel_epi ((triaQuotient A D S).map s')).1
  rw [← CategoryTheory.Functor.map_comp, hz', CategoryTheory.Functor.map_zero,
    Limits.comp_zero]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonFiniteRoof

/-! ## DerivedComparisonRepresentableHom（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonRepresentableHom.lean） -/

/-! # 商内の代表対象への射と制限代表加群への導来 Hom -/

@[expose] public section DerivedComparisonRepresentableHom
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定 Verdier 商の射を、代表加群比較の像に作用させる。 -/
def quotientRepresentableHomMap (S : Set D) (z : D) (X : TriaCategory A D)
    (f : (triaQuotient A D S).obj X ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z)) :
    (triaInclusion A D).obj X ⟶ (moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z)) :=
  quotientRestrictionLocalizedHomEquiv A D S z X
    ((quotientRestrictionLocalizedHom A D S z).map f.op
      ((quotientRestrictionLocalizedHomEquiv A D S z (triaRepresentable A D z)).symm
        ((moduleToDerived A D).map
          (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z))))

lemma quotientRepresentableHomMap_map (S : Set D) (z : D) {X : TriaCategory A D}
    (f : X ⟶ triaRepresentable A D z) :
    quotientRepresentableHomMap A D S z X ((triaQuotient A D S).map f) =
      (triaInclusion A D).map f ≫ (moduleToDerived A D).map
        (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z) := by
  unfold quotientRepresentableHomMap
  rw [quotientRestrictionLocalizedHomEquiv_naturality, Equiv.apply_symm_apply]

lemma quotientRepresentableHomMap_precomp (S : Set D) (z : D)
    {X Y : TriaCategory A D} (s : X ⟶ Y)
    (f : (triaQuotient A D S).obj Y ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z)) :
    quotientRepresentableHomMap A D S z X ((triaQuotient A D S).map s ≫ f) =
      (triaInclusion A D).map s ≫ quotientRepresentableHomMap A D S z Y f := by
  unfold quotientRepresentableHomMap
  rw [op_comp, CategoryTheory.Functor.map_comp]
  exact quotientRestrictionLocalizedHomEquiv_naturality A D S z s _

/-- 局所 K-flat 仮定の下で、この Hom 比較は全射。 -/
lemma quotientRepresentableHomMap_surjective (S : Set D)
    (h : localKFlat A D S) (z : D) (X : TriaCategory A D) :
    Function.Surjective (quotientRepresentableHomMap A D S z X) := by
  intro f
  obtain ⟨E, s, g, hs, hg⟩ := quotientRepresentable_exists_triaRoof A D S h z X f
  have : IsIso ((triaQuotient A D S).map s) :=
    Localization.inverts (triaQuotient A D S) (triaImage A D S).trW s hs
  let φ := inv ((triaQuotient A D S).map s) ≫ (triaQuotient A D S).map g
  refine ⟨φ, ?_⟩
  apply (quotientRepresentableRestriction_tria_precomp_bijective A D S z s hs).1
  dsimp only
  rw [← quotientRepresentableHomMap_precomp]
  have he : (triaQuotient A D S).map s ≫ φ = (triaQuotient A D S).map g := by
    simp [φ]
  rw [he, quotientRepresentableHomMap_map]
  exact hg

/-- 比較の値が零なら、Verdier 商の射そのものが零。 -/
lemma quotientRepresentableHomMap_eq_zero (S : Set D)
    (h : localKFlat A D S) (z : D) (X : TriaCategory A D)
    (f : (triaQuotient A D S).obj X ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z))
    (hf : quotientRepresentableHomMap A D S z X f = 0) : f = 0 := by
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction
    (triaQuotient A D S) (triaImage A D S).trW f
  have he : (triaQuotient A D S).map φ.s ≫ f = (triaQuotient A D S).map φ.f := by
    rw [hφ, MorphismProperty.RightFraction.map_s_comp_map]
  have hz : (triaInclusion A D).map φ.f ≫ (moduleToDerived A D).map
      (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z) = 0 := by
    rw [← quotientRepresentableHomMap_map, ← he, quotientRepresentableHomMap_precomp,
      hf, comp_zero]
  have hg := triaQuotient_map_eq_zero_of_representableComparison A D S h z _ φ.f hz
  have : IsIso ((triaQuotient A D S).map φ.s) :=
    Localization.inverts (triaQuotient A D S) (triaImage A D S).trW φ.s φ.hs
  apply (cancel_epi ((triaQuotient A D S).map φ.s)).1
  rw [he, hg, comp_zero]

/-- 二つの分数を共通の分母に揃え、元の射の差の核を消すと単射性が得られる。 -/
lemma quotientRepresentableHomMap_injective (S : Set D)
    (h : localKFlat A D S) (z : D) (X : TriaCategory A D) :
    Function.Injective (quotientRepresentableHomMap A D S z X) := by
  intro f g hfg
  let Q := triaQuotient A D S
  let W := (triaImage A D S).trW
  obtain ⟨α, hα⟩ := Localization.exists_rightFraction Q W f
  obtain ⟨β, hβ⟩ := Localization.exists_rightFraction Q W g
  obtain ⟨γ, hγ⟩ := (MorphismProperty.LeftFraction.mk α.s β.s β.hs).exists_rightFraction
  let t := γ.s ≫ α.s
  let a := γ.s ≫ α.f
  let b := γ.f ≫ β.f
  have ht : W t := W.comp_mem _ _ γ.hs α.hs
  have ha : Q.map t ≫ f = Q.map a := by
    dsimp only [t, a]
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
      hα, MorphismProperty.RightFraction.map_s_comp_map]
  have hb : Q.map t ≫ g = Q.map b := by
    dsimp only [t, b]
    rw [hγ, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      Category.assoc, hβ, MorphismProperty.RightFraction.map_s_comp_map]
  have he : (triaInclusion A D).map a ≫ (moduleToDerived A D).map
        (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z) =
      (triaInclusion A D).map b ≫ (moduleToDerived A D).map
        (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z) := by
    rw [← quotientRepresentableHomMap_map, ← quotientRepresentableHomMap_map, ← ha, ← hb,
      quotientRepresentableHomMap_precomp, quotientRepresentableHomMap_precomp, hfg]
  have hz : (triaInclusion A D).map (a - b) ≫ (moduleToDerived A D).map
      (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z) = 0 := by
    rw [Functor.map_sub, Preadditive.sub_comp, he, sub_self]
  have hab : Q.map a = Q.map b := by
    have hh := triaQuotient_map_eq_zero_of_representableComparison A D S h z _ (a - b) hz
    rw [Functor.map_sub, sub_eq_zero] at hh
    exact hh
  have : IsIso (Q.map t) := Localization.inverts Q W t ht
  apply (cancel_epi (Q.map t)).1
  exact ha.trans (hab.trans hb.symm)

/-- 局所 K-flat 版の代表対象を終域とする、指定 Verdier 商の実際の Hom 同値。 -/
def quotientRepresentableHomEquiv (S : Set D) (h : localKFlat A D S)
    (z : D) (X : TriaCategory A D) :
    ((triaQuotient A D S).obj X ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z)) ≃
    ((triaInclusion A D).obj X ⟶ (moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z))) :=
  Equiv.ofBijective (quotientRepresentableHomMap A D S z X)
    ⟨quotientRepresentableHomMap_injective A D S h z X,
      quotientRepresentableHomMap_surjective A D S h z X⟩

/-- 随伴によって、右辺を明示的 dg 商側の実際の導来 Hom に直す。 -/
def quotientDerivedRepresentableHomEquiv (S : Set D) (h : localKFlat A D S)
    (z : D) (X : TriaCategory A D) :
    ((triaQuotient A D S).obj X ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z)) ≃
    ((dgDerivedExtension A D (QuotientObject D S) (inclusion A D S)).obj
        ((triaInclusion A D).obj X) ⟶
      (moduleToDerived A (QuotientObject D S)).obj
        (ForgetEnrichment.of (Complex A) (representable A (⟨z⟩ : QuotientObject D S)))) :=
  (quotientRepresentableHomEquiv A D S h z X).trans
    ((Iso.homCongr (Iso.refl _) (dgDerivedRestrictionComputation A D (QuotientObject D S)
      (inclusion A D S) (ForgetEnrichment.of (Complex A)
        (representable A (⟨z⟩ : QuotientObject D S)))).symm).trans
      (dgDerivedExtensionHomEquiv A D (QuotientObject D S) (inclusion A D S)
        ((triaInclusion A D).obj X) _).symm)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonRepresentableHom

/-! ## DerivedComparisonHomNormalization（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonHomNormalization.lean） -/

/-! # Verdier Hom 同値と実際の導来延長の射写像

随伴の単位による代表同型の正規化を、局所 K-flat Hom 同値と接続する。
-/

@[expose] public section DerivedComparisonHomNormalization
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma quotientDerivedRepresentableHomEquiv_adjoint (S : Set D) (h : localKFlat A D S)
    (z : D) (X : TriaCategory A D)
    (f : (triaQuotient A D S).obj X ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z)) :
    dgDerivedExtensionHomEquiv A D (QuotientObject D S) (inclusion A D S)
      ((triaInclusion A D).obj X)
      ((moduleToDerived A (QuotientObject D S)).obj
        (ForgetEnrichment.of (Complex A) (representable A (⟨z⟩ : QuotientObject D S))))
      (quotientDerivedRepresentableHomEquiv A D S h z X f) =
    quotientRepresentableHomMap A D S z X f ≫
      (dgDerivedRestrictionComputation A D (QuotientObject D S) (inclusion A D S)
        (ForgetEnrichment.of (Complex A) (representable A (⟨z⟩ : QuotientObject D S)))).inv := by
  simp only [quotientDerivedRepresentableHomEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    Iso.homCongr, Equiv.coe_fn_mk, quotientRepresentableHomEquiv, Equiv.ofBijective_apply,
    Iso.refl_inv, Category.id_comp, Iso.symm_hom]

/-- 元の tria の射に対し、Hom 同値は実際の導来延長の射写像と一致する。 -/
lemma quotientDerivedRepresentableHomEquiv_map (S : Set D) (h : localKFlat A D S)
    (z : D) {X : TriaCategory A D} (f : X ⟶ triaRepresentable A D z) :
    quotientDerivedRepresentableHomEquiv A D S h z X ((triaQuotient A D S).map f) =
      (dgDerivedExtension A D (QuotientObject D S) (inclusion A D S)).map
        ((triaInclusion A D).map f) ≫
      (derivedExtensionRepresentableUnitIso A D (QuotientObject D S) (inclusion A D S) z).hom := by
  apply (dgDerivedExtensionHomEquiv A D (QuotientObject D S) (inclusion A D S) _ _).injective
  rw [quotientDerivedRepresentableHomEquiv_adjoint,
    dgDerivedExtensionHomEquiv_naturality_left,
    quotientRepresentableHomMap_map, Category.assoc]
  exact congrArg (fun t => (triaInclusion A D).map f ≫ t)
    (derivedExtensionRepresentableUnitIso_homEquiv A D (QuotientObject D S)
      (inclusion A D S) z).symm

/-- Verdier 商の任意の射に対する Hom 同値も、元の tria の射による前置と可換。 -/
lemma quotientDerivedRepresentableHomEquiv_precomp (S : Set D) (h : localKFlat A D S)
    (z : D) {X Y : TriaCategory A D} (s : X ⟶ Y)
    (f : (triaQuotient A D S).obj Y ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z)) :
    quotientDerivedRepresentableHomEquiv A D S h z X ((triaQuotient A D S).map s ≫ f) =
      (dgDerivedExtension A D (QuotientObject D S) (inclusion A D S)).map
        ((triaInclusion A D).map s) ≫ quotientDerivedRepresentableHomEquiv A D S h z Y f := by
  apply (dgDerivedExtensionHomEquiv A D (QuotientObject D S) (inclusion A D S) _ _).injective
  rw [quotientDerivedRepresentableHomEquiv_adjoint,
    dgDerivedExtensionHomEquiv_naturality_left, quotientDerivedRepresentableHomEquiv_adjoint,
    quotientRepresentableHomMap_precomp, Category.assoc]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonHomNormalization

/-! ## DerivedComparisonDerivedLift（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonDerivedLift.lean） -/

/-! # 実際の導来延長の Verdier 因子化と代表対象への射写像の全単射性 -/

@[expose] public section DerivedComparisonDerivedLift
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

local instance (S : Set D) :
    (dgDerivedExtension A D (QuotientObject D S) (inclusion A D S)).CommShift ℤ :=
  dgDerivedExtensionCommShift A D _ _
local instance (S : Set D) :
    (dgDerivedExtension A D (QuotientObject D S) (inclusion A D S)).IsTriangulated :=
  dgDerivedExtensionIsTriangulated A D _ _

instance derivedComparisonFromTriaCommShift (S : Set D) :
    (derivedComparisonFromTria A D S).CommShift ℤ := by
  dsimp [derivedComparisonFromTria]
  infer_instance
instance derivedComparisonFromTriaIsTriangulated (S : Set D) :
    (derivedComparisonFromTria A D S).IsTriangulated := by
  dsimp [derivedComparisonFromTria]
  infer_instance

lemma derivedComparisonFromTria_inverts (S : Set D) :
    (triaImage A D S).trW.IsInvertedBy (derivedComparisonFromTria A D S) := by
  intro X Y f hf
  apply (triangulatedKernel_trW_iff (derivedComparisonFromTria A D S) f).1
  exact (triaImage A D S).trW_monotone
    (fun X hX => derivedComparisonFromTria_kills A D S X hX) _ hf

/-- 普通の加群の導来延長を、指定 Verdier 商に沿って因子化した関手。 -/
def derivedQuotientLift (S : Set D) :
    TriaQuotient A D S ⥤ DerivedModuleCategory A (QuotientObject D S) :=
  Localization.lift (derivedComparisonFromTria A D S)
    (derivedComparisonFromTria_inverts A D S) (triaQuotient A D S)

def derivedQuotientLiftFactors (S : Set D) :
    triaQuotient A D S ⋙ derivedQuotientLift A D S ≅ derivedComparisonFromTria A D S :=
  Localization.fac (derivedComparisonFromTria A D S)
    (derivedComparisonFromTria_inverts A D S) (triaQuotient A D S)

/-- 因子化同型と代表対象の計算同型で移した、因子化関手の実際の射写像。 -/
def derivedQuotientLiftRepresentableMap (S : Set D) (z : D) (X : TriaCategory A D)
    (f : (triaQuotient A D S).obj X ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z)) :
    (derivedComparisonFromTria A D S).obj X ⟶
      (moduleToDerived A (QuotientObject D S)).obj
        (ForgetEnrichment.of (Complex A) (representable A (⟨z⟩ : QuotientObject D S))) :=
  (derivedQuotientLiftFactors A D S).inv.app X ≫ (derivedQuotientLift A D S).map f ≫
    (derivedQuotientLiftFactors A D S).hom.app (triaRepresentable A D z) ≫
      (derivedExtensionRepresentableUnitIso A D (QuotientObject D S) (inclusion A D S) z).hom

lemma derivedQuotientLiftRepresentableMap_map (S : Set D) (z : D)
    {X : TriaCategory A D} (f : X ⟶ triaRepresentable A D z) :
    derivedQuotientLiftRepresentableMap A D S z X ((triaQuotient A D S).map f) =
      (derivedComparisonFromTria A D S).map f ≫
        (derivedExtensionRepresentableUnitIso A D (QuotientObject D S)
          (inclusion A D S) z).hom := by
  have he := congrArg (fun t => t ≫
    (derivedExtensionRepresentableUnitIso A D (QuotientObject D S) (inclusion A D S) z).hom)
    (NatIso.naturality_1 (derivedQuotientLiftFactors A D S) f)
  simpa only [derivedQuotientLiftRepresentableMap, Category.assoc, Functor.comp_map] using he


lemma derivedQuotientLiftRepresentableMap_precomp (S : Set D) (z : D)
    {X Y : TriaCategory A D} (s : X ⟶ Y)
    (f : (triaQuotient A D S).obj Y ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z)) :
    derivedQuotientLiftRepresentableMap A D S z X ((triaQuotient A D S).map s ≫ f) =
      (derivedComparisonFromTria A D S).map s ≫
        derivedQuotientLiftRepresentableMap A D S z Y f := by
  unfold derivedQuotientLiftRepresentableMap
  rw [CategoryTheory.Functor.map_comp]
  have hn := (derivedQuotientLiftFactors A D S).inv.naturality s
  change (derivedComparisonFromTria A D S).map s ≫
      (derivedQuotientLiftFactors A D S).inv.app Y =
    (derivedQuotientLiftFactors A D S).inv.app X ≫
      (derivedQuotientLift A D S).map ((triaQuotient A D S).map s) at hn
  have he := congrArg (fun t => t ≫ (derivedQuotientLift A D S).map f ≫
    (derivedQuotientLiftFactors A D S).hom.app (triaRepresentable A D z) ≫
      (derivedExtensionRepresentableUnitIso A D (QuotientObject D S) (inclusion A D S) z).hom) hn
  simpa only [Category.assoc] using he.symm


/-- 右分数表示により、元の射上での一致は指定 Verdier 商の全ての射へ延びる。 -/
lemma derivedQuotientLiftRepresentableMap_eq (S : Set D) (h : localKFlat A D S)
    (z : D) (X : TriaCategory A D)
    (f : (triaQuotient A D S).obj X ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z)) :
    derivedQuotientLiftRepresentableMap A D S z X f =
      quotientDerivedRepresentableHomEquiv A D S h z X f := by
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction
    (triaQuotient A D S) (triaImage A D S).trW f
  have he : (triaQuotient A D S).map φ.s ≫ f = (triaQuotient A D S).map φ.f := by
    rw [hφ, MorphismProperty.RightFraction.map_s_comp_map]
  have : IsIso ((derivedComparisonFromTria A D S).map φ.s) :=
    derivedComparisonFromTria_inverts A D S φ.s φ.hs
  apply (cancel_epi ((derivedComparisonFromTria A D S).map φ.s)).1
  refine (derivedQuotientLiftRepresentableMap_precomp A D S z φ.s f).symm.trans ?_
  refine Eq.trans ?_ (quotientDerivedRepresentableHomEquiv_precomp A D S h z φ.s f)
  rw [he, derivedQuotientLiftRepresentableMap_map]
  exact (quotientDerivedRepresentableHomEquiv_map A D S h z φ.f).symm


lemma derivedQuotientLiftRepresentableMap_bijective (S : Set D) (h : localKFlat A D S)
    (z : D) (X : TriaCategory A D) :
    Function.Bijective (derivedQuotientLiftRepresentableMap A D S z X) := by
  have he : derivedQuotientLiftRepresentableMap A D S z X =
      quotientDerivedRepresentableHomEquiv A D S h z X := by
    funext f
    exact derivedQuotientLiftRepresentableMap_eq A D S h z X f
  rw [he]
  exact (quotientDerivedRepresentableHomEquiv A D S h z X).bijective

/-- 代表対象を終域とする、因子化関手そのものの射写像は全単射。 -/
lemma derivedQuotientLift_map_bijective_representable (S : Set D) (h : localKFlat A D S)
    (z : D) (X : TriaCategory A D) :
    Function.Bijective ((derivedQuotientLift A D S).map
      (X := (triaQuotient A D S).obj X)
      (Y := (triaQuotient A D S).obj (triaRepresentable A D z))) := by
  let eX := (derivedQuotientLiftFactors A D S).app X
  let eZ := (derivedQuotientLiftFactors A D S).app (triaRepresentable A D z) ≪≫
    derivedExtensionRepresentableUnitIso A D (QuotientObject D S) (inclusion A D S) z
  apply (Function.Bijective.of_comp_iff' (Iso.homCongr eX eZ).bijective _).1
  exact derivedQuotientLiftRepresentableMap_bijective A D S h z X

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonDerivedLift

/-! ## DerivedComparisonFullFaithful（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonFullFaithful.lean） -/

/-! # 局所 K-flat 版の実際の導来延長の Verdier 因子化の充満忠実性 -/

@[expose] public section DerivedComparisonFullFaithful
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance derivedQuotientLiftLifting (S : Set D) :
    Localization.Lifting (triaQuotient A D S) (triaImage A D S).trW
      (derivedComparisonFromTria A D S) (derivedQuotientLift A D S) :=
  Localization.liftingLift (derivedComparisonFromTria A D S)
    (derivedComparisonFromTria_inverts A D S) (triaQuotient A D S)

instance derivedQuotientLiftCommShift (S : Set D) :
    (derivedQuotientLift A D S).CommShift ℤ :=
  Functor.commShiftOfLocalization (triaQuotient A D S) (triaImage A D S).trW ℤ
    (derivedComparisonFromTria A D S) (derivedQuotientLift A D S)

instance derivedQuotientLiftFactorsCommShift (S : Set D) :
    NatTrans.CommShift (derivedQuotientLiftFactors A D S).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization (triaQuotient A D S) (triaImage A D S).trW ℤ
    (derivedComparisonFromTria A D S) (derivedQuotientLift A D S)

instance derivedQuotientLiftIsTriangulated (S : Set D) :
    (derivedQuotientLift A D S).IsTriangulated := by
  have : (triaQuotient A D S).mapArrow.EssSurj :=
    Localization.essSurj_mapArrow (triaQuotient A D S) (triaImage A D S).trW
  exact Functor.isTriangulated_of_precomp_iso (derivedQuotientLiftFactors A D S)

lemma derivedQuotientLift_representable_target (S : Set D) (h : localKFlat A D S) (z : D) :
    homComparisonTarget (derivedQuotientLift A D S)
      ((triaQuotient A D S).obj (triaRepresentable A D z)) := by
  intro X
  let Q := triaQuotient A D S
  exact homComparison_bijective_of_iso (derivedQuotientLift A D S)
    (Q.objObjPreimageIso X) (Iso.refl _)
    (derivedQuotientLift_map_bijective_representable A D S h z (Q.objPreimage X))

/-- 任意の始域から、代表対象の任意の整数 shift への射写像も全単射。 -/
lemma derivedQuotientLift_shifted_representable_target
    (S : Set D) (h : localKFlat A D S) (z : D) (n : ℤ) :
    homComparisonTarget (derivedQuotientLift A D S)
      (((triaQuotient A D S).obj (triaRepresentable A D z))⟦n⟧) :=
  (homComparisonTarget (derivedQuotientLift A D S)).le_shift n _
    (derivedQuotientLift_representable_target A D S h z)

/-- 終域に関する三角閉性と代表生成性により、全ての tria 対象間で全単射になる。 -/
lemma derivedQuotientLift_map_bijective (S : Set D) (h : localKFlat A D S)
    (X Y : TriaQuotient A D S) :
    Function.Bijective ((derivedQuotientLift A D S).map (X := X) (Y := Y)) := by
  let P := homComparisonTarget (derivedQuotientLift A D S)
  let : P.IsTriangulated := homComparisonTargetIsTriangulated _
  have hle : triaImage A D Set.univ ≤ P.inverseImage (triaQuotient A D S) :=
    (triaImage_le_iff_generators A D Set.univ (P.inverseImage (triaQuotient A D S))).2
      (fun z _ => derivedQuotientLift_representable_target A D S h z)
  let Q := triaQuotient A D S
  have hY : P (Q.obj (Q.objPreimage Y)) :=
    hle (Q.objPreimage Y) (Q.objPreimage Y).property
  exact P.prop_of_iso (Q.objObjPreimageIso Y) hY X

/-- 局所 K-flat 仮定を明示的に受け取る、実際の因子化関手の充満忠実性。 -/
def derivedQuotientLiftFullyFaithful (S : Set D) (h : localKFlat A D S) :
    (derivedQuotientLift A D S).FullyFaithful := by
  let : (derivedQuotientLift A D S).Full := {
    map_surjective := fun {X Y} f => (derivedQuotientLift_map_bijective A D S h X Y).2 f }
  let : (derivedQuotientLift A D S).Faithful := {
    map_injective := fun {X Y} f g he => (derivedQuotientLift_map_bijective A D S h X Y).1 he }
  exact Functor.FullyFaithful.ofFullyFaithful _

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonFullFaithful

/-! ## DerivedComparisonEquivalence（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonEquivalence.lean） -/

/-! # 局所 K-flat 版の tria(D)/tria(S) と tria(D/S) の同値 -/

@[expose] public section DerivedComparisonEquivalence
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma derivedQuotientLift_finiteCell (S : Set D) (X : TriaQuotient A D S) :
    derivedFiniteCellOver A (QuotientObject D S) Set.univ
      ((derivedQuotientLift A D S).obj X) := by
  let Q := triaQuotient A D S
  let P := derivedFiniteCellOver A (QuotientObject D S) Set.univ
  exact P.prop_of_iso ((derivedQuotientLift A D S).mapIso (Q.objObjPreimageIso X))
    (P.prop_of_iso ((derivedQuotientLiftFactors A D S).app (Q.objPreimage X)).symm
      (derivedComparisonFromTria_finiteCell A D S (Q.objPreimage X)))

/-- 指定 Verdier 商から明示的 dg 商の tria への実際の導来延長。 -/
def localQuotientTriaFunctor (S : Set D) :
    TriaQuotient A D S ⥤ TriaCategory A (QuotientObject D S) :=
  (derivedFiniteCellOver A (QuotientObject D S) Set.univ).lift
    (derivedQuotientLift A D S) (derivedQuotientLift_finiteCell A D S)

instance localQuotientTriaFunctorCommShift (S : Set D) :
    (localQuotientTriaFunctor A D S).CommShift ℤ := by
  dsimp [localQuotientTriaFunctor]
  infer_instance
instance localQuotientTriaFunctorIsTriangulated (S : Set D) :
    (localQuotientTriaFunctor A D S).IsTriangulated := by
  dsimp [localQuotientTriaFunctor]
  infer_instance

/-- 値域を充満部分圏に制限しても、同じ射写像の充満忠実性を保つ。 -/
def localQuotientTriaFullyFaithful (S : Set D) (h : localKFlat A D S) :
    (localQuotientTriaFunctor A D S).FullyFaithful where
  preimage f := (derivedQuotientLiftFullyFaithful A D S h).preimage
    ((triaInclusion A (QuotientObject D S)).map f)
  map_preimage f := by
    apply (triaInclusion A (QuotientObject D S)).map_injective
    exact (derivedQuotientLiftFullyFaithful A D S h).map_preimage _
  preimage_map f := (derivedQuotientLiftFullyFaithful A D S h).preimage_map f

/-- 商内の代表対象の像の具体的な計算。 -/
def localQuotientTriaRepresentableIso (S : Set D) (z : D) :
    (localQuotientTriaFunctor A D S).obj
        ((triaQuotient A D S).obj (triaRepresentable A D z)) ≅
      triaRepresentable A (QuotientObject D S) ⟨z⟩ :=
  (derivedFiniteCellOver A (QuotientObject D S) Set.univ).isoMk
    ((derivedQuotientLiftFactors A D S).app (triaRepresentable A D z) ≪≫
      derivedExtensionRepresentableUnitIso A D (QuotientObject D S) (inclusion A D S) z)

lemma localQuotientTriaFunctor_essSurj (S : Set D) (h : localKFlat A D S) :
    (localQuotientTriaFunctor A D S).EssSurj := by
  let : (localQuotientTriaFunctor A D S).Full := (localQuotientTriaFullyFaithful A D S h).full
  refine ⟨fun X => ?_⟩
  have hle := (triaImage_le_iff_generators A (QuotientObject D S) Set.univ
    (localQuotientTriaFunctor A D S).essImage).2 (fun z _ =>
      ⟨(triaQuotient A D S).obj (triaRepresentable A D z.val),
        ⟨localQuotientTriaRepresentableIso A D S z.val⟩⟩)
  exact hle X X.property

/-- 局所 K-flat 仮定から得る、指定 Verdier 商と明示的 dg 商の tria の同値。 -/
def localQuotientTriaEquivalence (S : Set D) (h : localKFlat A D S) :
    TriaQuotient A D S ≌ TriaCategory A (QuotientObject D S) := by
  let : (localQuotientTriaFunctor A D S).Full := (localQuotientTriaFullyFaithful A D S h).full
  let : (localQuotientTriaFunctor A D S).Faithful :=
    (localQuotientTriaFullyFaithful A D S h).faithful
  let : (localQuotientTriaFunctor A D S).EssSurj := localQuotientTriaFunctor_essSurj A D S h
  let : (localQuotientTriaFunctor A D S).IsEquivalence := {}
  exact (localQuotientTriaFunctor A D S).asEquivalence

/-- M9 の商を取る前の Hom が次数零に集中して平坦である場合の入口。 -/
def localQuotientTriaEquivalence_of_flat_zero (S : Set D)
    (hz : ∀ (x y : D) (i : ℤ), i ≠ 0 → IsZero ((x ⟶[Complex A] y).X i))
    (hf : ∀ x y : D, Module.Flat A ((x ⟶[Complex A] y).X 0)) :
    TriaQuotient A D S ≌ TriaCategory A (QuotientObject D S) :=
  localQuotientTriaEquivalence A D S
    (allHomKFlat_local A D (allHomKFlat_of_flat_zero A D hz hf) S)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonEquivalence

/-! ## DerivedComparisonPerfect（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonPerfect.lean） -/

/-! # 局所 K-flat 版の dg 商の perfect enhancement と完備 Verdier 商

U17a の指定 Karoubi 完備化に値を持ち、既存の順序交換比較に接続する。
-/

@[expose] public section DerivedComparisonPerfect
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Idempotents Functor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance localQuotientTriaEquivalenceFunctorCommShift (S : Set D) (h : localKFlat A D S) :
    (localQuotientTriaEquivalence A D S h).functor.CommShift ℤ := by
  change (localQuotientTriaFunctor A D S).CommShift ℤ
  infer_instance

instance localQuotientTriaEquivalenceInverseCommShift (S : Set D) (h : localKFlat A D S) :
    (localQuotientTriaEquivalence A D S h).inverse.CommShift ℤ :=
  (localQuotientTriaEquivalence A D S h).commShiftInverse ℤ

instance localQuotientTriaEquivalenceCommShift (S : Set D) (h : localKFlat A D S) :
    (localQuotientTriaEquivalence A D S h).CommShift ℤ :=
  (localQuotientTriaEquivalence A D S h).commShift_of_functor ℤ

instance localQuotientTriaEquivalenceFunctorIsTriangulated (S : Set D) (h : localKFlat A D S) :
    (localQuotientTriaEquivalence A D S h).functor.IsTriangulated := by
  change (localQuotientTriaFunctor A D S).IsTriangulated
  infer_instance

instance localQuotientTriaEquivalenceIsTriangulated (S : Set D) (h : localKFlat A D S) :
    (localQuotientTriaEquivalence A D S h).IsTriangulated :=
  Equivalence.IsTriangulated.mk' (localQuotientTriaEquivalence A D S h) inferInstance

/-- U15e の実際の同値を Karoubi 完備化した同値。 -/
def localCompletedQuotientEquivalence (S : Set D) (h : localKFlat A D S) :
    CompletedTriaQuotient A D S ≌ Karoubi (TriaCategory A (QuotientObject D S)) :=
  karoubiEquivalenceTransport (localQuotientTriaEquivalence A D S h)

instance localCompletedQuotientEquivalenceFunctorCommShift (S : Set D) (h : localKFlat A D S) :
    (localCompletedQuotientEquivalence A D S h).functor.CommShift ℤ := by
  change ((functorExtension₂ _ _).obj (localQuotientTriaEquivalence A D S h).functor).CommShift ℤ
  infer_instance

instance localCompletedQuotientEquivalenceInverseCommShift (S : Set D) (h : localKFlat A D S) :
    (localCompletedQuotientEquivalence A D S h).inverse.CommShift ℤ :=
  (localCompletedQuotientEquivalence A D S h).commShiftInverse ℤ

instance localCompletedQuotientEquivalenceCommShift (S : Set D) (h : localKFlat A D S) :
    (localCompletedQuotientEquivalence A D S h).CommShift ℤ :=
  (localCompletedQuotientEquivalence A D S h).commShift_of_functor ℤ

instance localCompletedQuotientEquivalenceIsTriangulated (S : Set D) (h : localKFlat A D S) :
    (localCompletedQuotientEquivalence A D S h).IsTriangulated :=
  Equivalence.IsTriangulated.mk' (localCompletedQuotientEquivalence A D S h) (by
    change ((functorExtension₂ _ _).obj
      (localQuotientTriaEquivalence A D S h).functor).IsTriangulated
    infer_instance)

/-- U17b：明示的 dg 商の perfect enhancement の H⁰ と指定完備 Verdier 商の同値。 -/
def localPerfectQuotientEquivalence (S : Set D) (h : localKFlat A D S) :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ≌
      CompletedTriaQuotient A D S :=
  ((perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).trans
    (finiteCellKaroubiPerfectEquivalence A (QuotientObject D S) Set.univ).symm).trans
      (localCompletedQuotientEquivalence A D S h).symm

instance localPerfectQuotientEquivalenceFunctorCommShift (S : Set D) (h : localKFlat A D S) :
    (localPerfectQuotientEquivalence A D S h).functor.CommShift ℤ := by
  dsimp [localPerfectQuotientEquivalence]
  infer_instance

instance localPerfectQuotientEquivalenceInverseCommShift (S : Set D) (h : localKFlat A D S) :
    (localPerfectQuotientEquivalence A D S h).inverse.CommShift ℤ :=
  (localPerfectQuotientEquivalence A D S h).commShiftInverse ℤ

instance localPerfectQuotientEquivalenceCommShift (S : Set D) (h : localKFlat A D S) :
    (localPerfectQuotientEquivalence A D S h).CommShift ℤ :=
  (localPerfectQuotientEquivalence A D S h).commShift_of_functor ℤ

instance localPerfectQuotientEquivalenceFunctorIsTriangulated
    (S : Set D) (h : localKFlat A D S) :
    (localPerfectQuotientEquivalence A D S h).functor.IsTriangulated := by
  change (((perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor ⋙
    (finiteCellKaroubiPerfectEquivalence A (QuotientObject D S) Set.univ).inverse) ⋙
      (localCompletedQuotientEquivalence A D S h).inverse).IsTriangulated
  infer_instance

instance localPerfectQuotientEquivalenceIsTriangulated (S : Set D) (h : localKFlat A D S) :
    (localPerfectQuotientEquivalence A D S h).IsTriangulated :=
  Equivalence.IsTriangulated.mk' (localPerfectQuotientEquivalence A D S h) inferInstance

/-- 小さい dg 代表系の H⁰ を用いた、同じ指定完備 Verdier 商との比較。 -/
def localSmallPerfectQuotientEquivalence (S : Set D) (h : localKFlat A D S) :
    SmallPerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ≌
      CompletedTriaQuotient A D S :=
  ((smallPerfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).trans
    (finiteCellKaroubiPerfectEquivalence A (QuotientObject D S) Set.univ).symm).trans
      (localCompletedQuotientEquivalence A D S h).symm

instance localSmallPerfectQuotientEquivalenceFunctorCommShift (S : Set D) (h : localKFlat A D S) :
    (localSmallPerfectQuotientEquivalence A D S h).functor.CommShift ℤ := by
  dsimp [localSmallPerfectQuotientEquivalence]
  infer_instance

instance localSmallPerfectQuotientEquivalenceInverseCommShift (S : Set D) (h : localKFlat A D S) :
    (localSmallPerfectQuotientEquivalence A D S h).inverse.CommShift ℤ :=
  (localSmallPerfectQuotientEquivalence A D S h).commShiftInverse ℤ

instance localSmallPerfectQuotientEquivalenceCommShift (S : Set D) (h : localKFlat A D S) :
    (localSmallPerfectQuotientEquivalence A D S h).CommShift ℤ :=
  (localSmallPerfectQuotientEquivalence A D S h).commShift_of_functor ℤ

instance localSmallPerfectQuotientEquivalenceFunctorIsTriangulated
    (S : Set D) (h : localKFlat A D S) :
    (localSmallPerfectQuotientEquivalence A D S h).functor.IsTriangulated := by
  change (((smallPerfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor ⋙
    (finiteCellKaroubiPerfectEquivalence A (QuotientObject D S) Set.univ).inverse) ⋙
      (localCompletedQuotientEquivalence A D S h).inverse).IsTriangulated
  infer_instance

instance localSmallPerfectQuotientEquivalenceIsTriangulated (S : Set D) (h : localKFlat A D S) :
    (localSmallPerfectQuotientEquivalence A D S h).IsTriangulated :=
  Equivalence.IsTriangulated.mk' (localSmallPerfectQuotientEquivalence A D S h) inferInstance

/-- 同じ比較の、完備化を先に行う側への表示。 -/
def localPerfectKaroubiFirstEquivalence (S : Set D) (h : localKFlat A D S) :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ≌
      Karoubi (KaroubiFirstQuotient (triaImage A D S)) :=
  (localPerfectQuotientEquivalence A D S h).trans (triaKaroubiOrderEquivalence A D S).symm

/-- U17c の既存の順序交換比較を、局所 K-flat perfect enhancement の比較へ後置する。 -/
def localPerfectPaperSequenceComparison (S : Set D) (h : localKFlat A D S) :
    triaKaroubiFirst A D S ⋙ (triaKaroubiOrderEquivalence A D S).functor ⋙
        (localPerfectQuotientEquivalence A D S h).inverse ≅
      triaQuotient A D S ⋙ toKaroubi _ ⋙
        (localPerfectQuotientEquivalence A D S h).inverse :=
  isoWhiskerRight (triaKaroubiComparison A D S)
    (localPerfectQuotientEquivalence A D S h).inverse

/-- M9 の次数零の平坦 Hom を入力とする U17b の同値。 -/
def localPerfectQuotientEquivalence_of_flat_zero (S : Set D)
    (hz : ∀ (x y : D) (i : ℤ), i ≠ 0 → Limits.IsZero ((x ⟶[Complex A] y).X i))
    (hf : ∀ x y : D, Module.Flat A ((x ⟶[Complex A] y).X 0)) :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ≌
      CompletedTriaQuotient A D S :=
  localPerfectQuotientEquivalence A D S
    (allHomKFlat_local A D (allHomKFlat_of_flat_zero A D hz hf) S)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonPerfect

/-! ## DerivedComparisonExtensionCoherence（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonExtensionCoherence.lean） -/

/-! # 導来延長とホモトピー有限 cell 上の underived 延長の自然同型 -/

@[expose] public section DerivedComparisonExtensionCoherence
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Functor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

private lemma comparison_naturality
    {C₀ C₁ T₀ T₁ : Type*} [Category* C₀] [Category* C₁] [Category* T₀] [Category* T₁]
    (Q : C₀ ⥤ T₀) (P : C₁ ⥤ T₁) (G : C₀ ⥤ C₁) (R₀ : C₁ ⥤ C₀)
    (L : T₀ ⥤ T₁) (R : T₁ ⥤ T₀) (a : G ⊣ R₀) (b : L ⊣ R)
    (c : ∀ N, R.obj (P.obj N) ≅ Q.obj (R₀.obj N))
    (δ : ∀ M, L.obj (Q.obj M) ⟶ P.obj (G.obj M))
    (hδ : ∀ M N (s : G.obj M ⟶ N),
      b.homEquiv _ _ (δ M ≫ P.map s) = Q.map (a.homEquiv _ _ s) ≫ (c N).inv)
    {M N : C₀} (f : M ⟶ N) :
    L.map (Q.map f) ≫ δ N = δ M ≫ P.map (G.map f) := by
  have hi : b.homEquiv _ _ (δ N) = Q.map (a.homEquiv _ _ (𝟙 (G.obj N))) ≫
      (c (G.obj N)).inv := by
    simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using hδ N (G.obj N) (𝟙 _)
  apply (b.homEquiv _ _).injective
  rw [b.homEquiv_naturality_left, hi, hδ]
  have hn := a.homEquiv_naturality_left f (𝟙 (G.obj N))
  simp only [Category.comp_id] at hn
  rw [hn, CategoryTheory.Functor.map_comp, Category.assoc]

lemma derivedExtensionUnderivedMap_naturality {M N : ModuleCategory A D} (f : M ⟶ N) :
    (dgDerivedExtension A D E F).map ((moduleToDerived A D).map f) ≫
        derivedExtensionUnderivedMap A D E F N =
      derivedExtensionUnderivedMap A D E F M ≫
        (moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map f) := by
  exact comparison_naturality (moduleToDerived A D) (moduleToDerived A E)
    (dgModuleExtension A D E F).onClosed (dgModuleRestriction A D E F.op).onClosed
    (dgDerivedExtension A D E F) (dgDerivedRestriction A D E F)
    (dgModuleEnrichedRestrictionAdjunction A D E F)
    (dgDerivedExtensionRestrictionAdjunction A D E F)
    (dgDerivedRestrictionComputation A D E F) (derivedExtensionUnderivedMap A D E F)
    (fun M N s => by
      rw [dgDerivedExtensionRestrictionAdjunction_homEquiv]
      exact derivedExtensionUnderivedMap_homEquiv A D E F M N s) f

def derivedExtensionUnderivedNatTrans :
    moduleToDerived A D ⋙ dgDerivedExtension A D E F ⟶
      (dgModuleExtension A D E F).onClosed ⋙ moduleToDerived A E where
  app M := derivedExtensionUnderivedMap A D E F M
  naturality _ _ f := derivedExtensionUnderivedMap_naturality A D E F f

def extensionHomotopyComputationNatIso :
    moduleToHomotopy A D ⋙ dgExtensionHomotopyToDerived A D E F ≅
      (dgModuleExtension A D E F).onClosed ⋙ moduleToDerived A E :=
  NatIso.ofComponents (dgExtensionHomotopyComputation A D E F)
    (fun f => dgExtensionHomotopyComputation_naturality A D E F f)

/-- 導来化からホモトピー圏上の延長への比較を、商関手の前置の充満性で降ろす。 -/
def homotopyDerivedExtensionComparison :
    moduleHomotopyToDerivedClosed A D ⋙ dgDerivedExtension A D E F ⟶
      dgExtensionHomotopyToDerived A D E F :=
  ((whiskeringLeft _ _ _).obj (moduleToHomotopy A D)).preimage
    ((isoWhiskerRight (moduleToHomotopyDerivedIso A D) (dgDerivedExtension A D E F)).hom ≫
      derivedExtensionUnderivedNatTrans A D E F ≫
        (extensionHomotopyComputationNatIso A D E F).inv)

lemma homotopyDerivedExtensionComparison_app (M : ModuleCategory A D) :
    (homotopyDerivedExtensionComparison A D E F).app ((moduleToHomotopy A D).obj M) =
      (dgDerivedExtension A D E F).map ((moduleToHomotopyDerivedIso A D).hom.app M) ≫
        derivedExtensionUnderivedMap A D E F M ≫
          (dgExtensionHomotopyComputation A D E F M).inv := by
  exact congrArg (fun τ => τ.app M)
    (((whiskeringLeft _ _ _).obj (moduleToHomotopy A D)).map_preimage
      (X := moduleHomotopyToDerivedClosed A D ⋙ dgDerivedExtension A D E F)
      (Y := dgExtensionHomotopyToDerived A D E F)
      ((isoWhiskerRight (moduleToHomotopyDerivedIso A D) (dgDerivedExtension A D E F)).hom ≫
        derivedExtensionUnderivedNatTrans A D E F ≫
          (extensionHomotopyComputationNatIso A D E F).inv))

lemma homotopyDerivedExtensionComparison_isIso {S : Set D}
    (X : HomotopyFiniteCellCategoryOver A D S) :
    IsIso ((homotopyDerivedExtensionComparison A D E F).app X.obj) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := X.property
  have hi : IsIso ((homotopyDerivedExtensionComparison A D E F).app
      ((moduleToHomotopy A D).obj M)) := by
    rw [homotopyDerivedExtensionComparison_app]
    let := derivedExtensionUnderivedMap_isIso A D E F M
      (moduleFiniteCellOver_homotopicallyProjective A D hM)
    infer_instance
  let := hi
  have hn := (homotopyDerivedExtensionComparison A D E F).naturality e.hom
  have hc : IsIso ((moduleHomotopyToDerivedClosed A D ⋙ dgDerivedExtension A D E F).map e.hom ≫
      (homotopyDerivedExtensionComparison A D E F).app X.obj) := by
    rw [hn]
    infer_instance
  let := hc
  exact IsIso.of_isIso_comp_left
    ((moduleHomotopyToDerivedClosed A D ⋙ dgDerivedExtension A D E F).map e.hom) _

/-- 有限 cell 部分圏上での、二つの延長計算の実際の自然同型。 -/
def finiteCellHomotopyDerivedExtensionIso (S : Set D) :
    (homotopyFiniteCellOver A D S).ι ⋙ moduleHomotopyToDerivedClosed A D ⋙
        dgDerivedExtension A D E F ≅
      (homotopyFiniteCellOver A D S).ι ⋙ dgExtensionHomotopyToDerived A D E F := by
  let τ := whiskerLeft (homotopyFiniteCellOver A D S).ι
    (homotopyDerivedExtensionComparison A D E F)
  let : ∀ X, IsIso (τ.app X) := fun X => homotopyDerivedExtensionComparison_isIso A D E F X
  let := NatIso.isIso_of_isIso_app τ
  exact asIso τ

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonExtensionCoherence

/-! ## DerivedComparisonCanonical（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonCanonical.lean） -/

/-! # 既存の有限 cell 比較と導来延長による比較の自然同型

指定 Verdier 商上の既存の比較関手そのものへ、局所 K-flat の同値を移す。
-/

@[expose] public section DerivedComparisonCanonical
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Functor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- tria 上の二つの導来加群圏への比較は自然同型。 -/
def quotientTriaDerivedModelsIso (S : Set D) :
    derivedComparisonFromTria A D S ≅ quotientTriaToDerived A D S := by
  let e := homotopyFiniteCellTriaEquivalence A D Set.univ
  let G := derivedComparisonFromTria A D S
  let hc : e.functor ⋙ G ≅ quotientCellToDerived A D S :=
    finiteCellHomotopyDerivedExtensionIso A D (QuotientObject D S) (inclusion A D S) Set.univ
  exact (isoWhiskerRight e.counitIso G).symm ≪≫ isoWhiskerLeft e.inverse hc

/-- 商側の tria に制限した同じ自然同型。 -/
def quotientTriaModelsIso (S : Set D) :
    derivedComparisonTria A D S ≅ quotientTriaFunctor A D S :=
  ((whiskeringRight _ _ _).obj (triaInclusion A (QuotientObject D S))).preimageIso
    (X := derivedComparisonTria A D S) (Y := quotientTriaFunctor A D S)
    (quotientTriaDerivedModelsIso A D S)

/-- 導来延長から作った tria 比較の、指定 Verdier 局所化による因子化。 -/
def localQuotientTriaFactors (S : Set D) :
    triaQuotient A D S ⋙ localQuotientTriaFunctor A D S ≅ derivedComparisonTria A D S :=
  ((whiskeringRight _ _ _).obj (triaInclusion A (QuotientObject D S))).preimageIso
    (X := triaQuotient A D S ⋙ localQuotientTriaFunctor A D S)
    (Y := derivedComparisonTria A D S) (derivedQuotientLiftFactors A D S)

/-- 指定 Verdier 商上の、二つの実際の比較関手の自然同型。 -/
def quotientComparisonModelsIso (S : Set D) :
    localQuotientTriaFunctor A D S ≅ quotientVerdierComparison A D S :=
  (Localization.fullyFaithfulWhiskeringLeft
    (triaQuotient A D S) (triaImage A D S).trW _).preimageIso
    (localQuotientTriaFactors A D S ≪≫ quotientTriaModelsIso A D S ≪≫
      (quotientVerdierComparisonFactors A D S).symm)

/-- 既存の指定比較関手そのものの、局所 K-flat 仮定下の充満忠実性。 -/
def quotientVerdierComparisonFullyFaithful (S : Set D) (h : localKFlat A D S) :
    (quotientVerdierComparison A D S).FullyFaithful :=
  (localQuotientTriaFullyFaithful A D S h).ofIso (quotientComparisonModelsIso A D S)

/-- 有限 cell のホモトピー圏モデルを使う既存の比較関手を関手部分とする同値。 -/
def quotientVerdierLocalEquivalence (S : Set D) (h : localKFlat A D S) :
    TriaQuotient A D S ≌ TriaCategory A (QuotientObject D S) :=
  (localQuotientTriaEquivalence A D S h).changeFunctor (quotientComparisonModelsIso A D S)

instance quotientVerdierLocalEquivalenceFunctorCommShift (S : Set D) (h : localKFlat A D S) :
    (quotientVerdierLocalEquivalence A D S h).functor.CommShift ℤ := by
  change (quotientVerdierComparison A D S).CommShift ℤ
  infer_instance
instance quotientVerdierLocalEquivalenceInverseCommShift (S : Set D) (h : localKFlat A D S) :
    (quotientVerdierLocalEquivalence A D S h).inverse.CommShift ℤ :=
  (quotientVerdierLocalEquivalence A D S h).commShiftInverse ℤ
instance quotientVerdierLocalEquivalenceCommShift (S : Set D) (h : localKFlat A D S) :
    (quotientVerdierLocalEquivalence A D S h).CommShift ℤ :=
  (quotientVerdierLocalEquivalence A D S h).commShift_of_functor ℤ
instance quotientVerdierLocalEquivalenceFunctorIsTriangulated (S : Set D) (h : localKFlat A D S) :
    (quotientVerdierLocalEquivalence A D S h).functor.IsTriangulated := by
  change (quotientVerdierComparison A D S).IsTriangulated
  infer_instance
instance quotientVerdierLocalEquivalenceIsTriangulated (S : Set D) (h : localKFlat A D S) :
    (quotientVerdierLocalEquivalence A D S h).IsTriangulated :=
  Equivalence.IsTriangulated.mk' (quotientVerdierLocalEquivalence A D S h) inferInstance

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonCanonical

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Drinfeld "Thm 3.4" (partial := component) "仮定：片側に関する局所 K 平坦性を課した dg 商（原典の平坦性側の設定）。結論：前三角・導来三角模型での Verdier 商との同値（原典の同値の対応部分）。"] _root_.SerrePositivity.DifferentialGraded.DGQuotient.localQuotientTriaEquivalence
