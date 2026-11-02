module

public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionRepresentable
public import SerrePositivity.DifferentialGraded.Endomorphism.Perfect
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import SerrePositivity.DifferentialGraded.Quotient.Path.Evaluation
public import SerrePositivity.DifferentialGraded.Module.YonedaFunctor
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.ColimitCones
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Filtration
public import SerrePositivity.DifferentialGraded.Module.RestrictionRepresentable
public import SerrePositivity.DifferentialGraded.Module.EvaluationReflects
public import SerrePositivity.DifferentialGraded.Verdier.Derived
public import SerrePositivity.DifferentialGraded.Category.ComplexHomotopyComparison
public import SerrePositivity.DifferentialGraded.Derived.Restriction
public import SerrePositivity.DifferentialGraded.Derived.Evaluation
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology
public import SerrePositivity.DifferentialGraded.Quotient.Path.Construction
public import SerrePositivity.DifferentialGraded.Module.Free
public import SerrePositivity.DifferentialGraded.Complexes.TensorRightComposition
public import SerrePositivity.DifferentialGraded.Complexes.RightTripleCochainExt
public import SerrePositivity.DifferentialGraded.Module.ActionChain
public import SerrePositivity.DifferentialGraded.Derived.RestrictionShift
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import Mathlib.CategoryTheory.Localization.Opposite
public import SerrePositivity.DifferentialGraded.Module.Colimits
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Connected

/-!
# Quotient.DerivedComparison.LocalFlatness

## 概要
局所 K-flat 条件、有限 cell・三角比較と局所 Homをまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## DerivedComparisonCells（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonCells.lean） -/

/-! # graph tensor の有限 cell 像

dg 圏の分解は使わず、加群の射影置換と有限操作の木を使う。
-/

@[expose] public section DerivedComparisonCells
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- shift、有限和、標準 cone を保存する加群上の関手に対する有限操作の帰納法。 -/
lemma finiteCellCode_image_mem
    (H : ModuleCategory A D ⥤ DerivedModuleCategory A E) [H.Additive] [H.CommShift ℤ]
    (hcone : ∀ {M N : ModuleCategory A D} (f : M ⟶ N),
      H.mapTriangle.obj (moduleConeTriangle A D f) ∈ distTriang (DerivedModuleCategory A E))
    (P : ObjectProperty (DerivedModuleCategory A E)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] {S : Set D}
    (hgen : ∀ x ∈ S, P (H.obj (ForgetEnrichment.of (Complex A) (representable A x))))
    {M : ModuleCategory A D} (c : ModuleFiniteCellCode A D S M) : P (H.obj M) := by
  induction c with
  | zero => exact P.prop_of_isZero (H.map_isZero (moduleZero_isZero A D))
  | generator x hx => exact hgen x hx
  | @shift M s c ih =>
    exact P.prop_of_iso ((H.commShiftIso s).app M).symm (P.le_shift s _ ih)
  | @sum M N c d ihc ihd =>
    have : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts H
    have h := P.ext_of_isTriangulatedClosed₂'
      (binaryBiproductTriangle (H.obj M) (H.obj N))
      (binaryBiproductTriangle_distinguished _ _) ihc ihd
    rw [ObjectProperty.isoClosure_eq_self] at h
    exact P.prop_of_iso (H.mapIso (moduleBiprodIso A D M N) ≪≫ H.mapBiprod M N).symm h
  | cone c d f ihc ihd =>
    have h := P.ext_of_isTriangulatedClosed₃' _ (hcone f) ihc ihd
    rw [ObjectProperty.isoClosure_eq_self] at h
    exact h
  | iso c e ih => exact P.prop_of_iso (H.mapIso e) ih

variable (F : DGFunctor A D E)
local instance : (dgModuleExtension A D E F).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A D E (dgModuleExtension A D E F)

/-- graph tensor の閉零関手の標準 cone 像は主導来圏で distinguished。 -/
lemma graphExtension_cone_distinguished {M N : ModuleCategory A D} (f : M ⟶ N) :
    ((dgModuleExtension A D E F).onClosed ⋙ moduleToDerived A E).mapTriangle.obj
      (moduleConeTriangle A D f) ∈ distTriang (DerivedModuleCategory A E) := by
  exact isomorphic_distinguished _ (moduleDerivedConeTriangle_distinguished A E
    ((dgModuleExtension A D E F).onClosed.map f)) _
    ((Functor.mapTriangleCompIso _ _).app _ ≪≫
      (moduleToDerived A E).mapTriangle.mapIso
        (dgModuleFunctorConeTriangleIso A D E (dgModuleExtension A D E F) f).symm)

/-- 射影置換を用いる導来拡張は、指定代表対象で検証した三角部分圏へ有限 cell を送る。 -/
lemma graphDerivedExtension_finiteCell_mem
    (P : ObjectProperty (DerivedModuleCategory A E)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] (S : Set D)
    (hgen : ∀ x ∈ S, P ((moduleToDerived A E).obj
      (ForgetEnrichment.of (Complex A) (representable A (F.obj x)))))
    {M : ModuleCategory A D} (hM : moduleFiniteCellOver A D S M) :
    P ((dgDerivedExtension A D E F).obj ((moduleToDerived A D).obj M)) := by
  obtain ⟨c⟩ := hM
  have h := finiteCellCode_image_mem A D E
    ((dgModuleExtension A D E F).onClosed ⋙ moduleToDerived A E)
    (graphExtension_cone_distinguished A D E F) P
    (fun x hx => P.prop_of_iso
      ((moduleToDerived A E).mapIso (dgModuleExtensionRepresentableIso A D E F x)).symm
      (hgen x hx)) c
  exact P.prop_of_iso
    (dgDerivedExtensionResolutionComputation A D E F
      (moduleIdentityProjectiveResolution A D M
        (moduleFiniteCellOver_homotopicallyProjective A D ⟨c⟩))).symm h

/-- 導来有限 cell の本質像についても、同じ代表対象による判定が使える。 -/
lemma graphDerivedExtension_derivedFiniteCell_mem
    (P : ObjectProperty (DerivedModuleCategory A E)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] (S : Set D)
    (hgen : ∀ x ∈ S, P ((moduleToDerived A E).obj
      (ForgetEnrichment.of (Complex A) (representable A (F.obj x)))))
    {X : DerivedModuleCategory A D} (hX : derivedFiniteCellOver A D S X) :
    P ((dgDerivedExtension A D E F).obj X) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hX
  exact P.prop_of_iso ((dgDerivedExtension A D E F).mapIso e)
    (graphDerivedExtension_finiteCell_mem A D E F P S hgen hM)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonCells

/-! ## DerivedComparisonFlatness（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonFlatness.lean） -/

/-! # 明示的 dg 商の導来比較に用いる片側の局所 K-flat 仮定

全ての x と b に対して同じ向きを選ぶ二条件を分ける。
ここでは比較定理そのものは仮定せず、Hom の A 上の K-flat 性だけを記述する。
-/

@[expose] public section DerivedComparisonFlatness
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 全対象から殺す対象への Hom が A 上 K-flat。 -/
def homIntoKFlat (S : Set D) : Prop :=
  ∀ (x : D) (b : S), complexKFlat A (x ⟶[Complex A] b.val)

/-- 殺す対象から全対象への Hom が A 上 K-flat。 -/
def homOutOfKFlat (S : Set D) : Prop :=
  ∀ (b : S) (x : D), complexKFlat A (b.val ⟶[Complex A] x)

/-- 二つの片側条件のいずれか。組ごとの選言ではない。 -/
def localKFlat (S : Set D) : Prop := homIntoKFlat A D S ∨ homOutOfKFlat A D S

/-- 全 Hom が係数環上 K-flat である条件。 -/
def allHomKFlat : Prop := ∀ x y : D, complexKFlat A (x ⟶[Complex A] y)

lemma homIntoKFlat_mono {S T : Set D} (h : S ⊆ T) (hT : homIntoKFlat A D T) :
    homIntoKFlat A D S := fun x b => hT x ⟨b.val, h b.property⟩

lemma homOutOfKFlat_mono {S T : Set D} (h : S ⊆ T) (hT : homOutOfKFlat A D T) :
    homOutOfKFlat A D S := fun b x => hT ⟨b.val, h b.property⟩ x

lemma localKFlat_mono {S T : Set D} (h : S ⊆ T) (hT : localKFlat A D T) :
    localKFlat A D S :=
  hT.elim (fun hT => Or.inl (homIntoKFlat_mono A D h hT))
    (fun hT => Or.inr (homOutOfKFlat_mono A D h hT))

lemma allHomKFlat_into (h : allHomKFlat A D) (S : Set D) : homIntoKFlat A D S :=
  fun x b => h x b.val

lemma allHomKFlat_outOf (h : allHomKFlat A D) (S : Set D) : homOutOfKFlat A D S :=
  fun b x => h b.val x

lemma allHomKFlat_local (h : allHomKFlat A D) (S : Set D) : localKFlat A D S :=
  Or.inl (allHomKFlat_into A D h S)

/-- Hom ごとの有界範囲は一様でなくてよい。非有界な試験複体に対する K-flat 性を得る。 -/
lemma allHomKFlat_of_flat_bounds
    (a b : D → D → ℤ)
    (ha : ∀ x y i, i < a x y → IsZero ((x ⟶[Complex A] y).X i))
    (hb : ∀ x y i, b x y < i → IsZero ((x ⟶[Complex A] y).X i))
    (hf : ∀ (x y : D) (i : ℤ), Module.Flat A ((x ⟶[Complex A] y).X i)) : allHomKFlat A D :=
  fun x y => complexKFlat_of_flat_bounds A _ (a x y) (b x y) (ha x y) (hb x y) (hf x y)

/-- M9 の商を取る前の dg 圏に適用する、次数零で平坦な Hom の入口。 -/
lemma allHomKFlat_of_flat_degreeZero
    (hz : ∀ (x y : D) (i : ℤ), i ≠ 0 → IsZero ((x ⟶[Complex A] y).X i))
    (hf : ∀ (x y : D) (i : ℤ), Module.Flat A ((x ⟶[Complex A] y).X i)) : allHomKFlat A D :=
  allHomKFlat_of_flat_bounds A D (fun _ _ => 0) (fun _ _ => 0)
    (fun x y i hi => hz x y i (ne_of_lt hi))
    (fun x y i hi => hz x y i (ne_of_gt hi)) hf

/-- 非零次数の平坦性は追加仮定せず、次数零の平坦性だけを要求する M9 用の形。 -/
lemma allHomKFlat_of_flat_zero
    (hz : ∀ (x y : D) (i : ℤ), i ≠ 0 → IsZero ((x ⟶[Complex A] y).X i))
    (hf : ∀ x y : D, Module.Flat A ((x ⟶[Complex A] y).X 0)) : allHomKFlat A D := by
  apply allHomKFlat_of_flat_degreeZero A D hz
  intro x y i
  by_cases hi : i = 0
  · subst i
    exact hf x y
  · have : Subsingleton ((x ⟶[Complex A] y).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp (hz x y i hi)
    infer_instance

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonFlatness

/-! ## DerivedComparisonContraction（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonContraction.lean） -/

/-! # 明示的 dg 商が殺す代表対象

指定 ε の境界式を既存 H⁰ 商へ渡し、dg Yoneda と主導来局所化で零性を運ぶ。
この段階には局所 K-flat 仮定を用いない。
-/

@[expose] public section DerivedComparisonContraction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 単位が境界である対象は、既存の H⁰ で零対象になる。 -/
lemma homotopy_isZero_of_unit_boundary (x : D)
    (h : (homObject A D x x).X (-1))
    (dh : (homObject A D x x).d (-1) 0 h = (unitElement A x).val) :
    IsZero ((toHomotopy A D).obj (ForgetEnrichment.of (Complex A) x)) := by
  apply (IsZero.iff_id_eq_zero _).2
  rw [← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_zero]
  apply (toHomotopy_map_eq_iff_boundary A D _ _).2
  refine ⟨h, ?_⟩
  change (homObject A D x x).d (-1) 0 h = (unitElement A x).val - 0
  simpa only [sub_zero] using dh

variable [Small.{u} D]

instance quotientObjectSmall (S : Set D) : Small.{u} (QuotientObject D S) :=
  small_of_injective (f := fun x : QuotientObject D S => x.val)
    (fun ⟨x⟩ ⟨y⟩ h => by cases h; rfl)

lemma quotientObject_homotopy_isZero (S : Set D) (b : S) :
    IsZero ((toHomotopy A (QuotientObject D S)).obj
      (ForgetEnrichment.of (Complex A) (⟨b.val⟩ : QuotientObject D S))) :=
  homotopy_isZero_of_unit_boundary A (QuotientObject D S) ⟨b.val⟩
    (epsilonElement A D S b) (differential_epsilonElement A D S b)

/-- 零になる対象の代表加群も、主導来圏で零になる。 -/
lemma representable_derived_isZero_of_unit_boundary (x : D)
    (h : (homObject A D x x).X (-1))
    (dh : (homObject A D x x).d (-1) 0 h = (unitElement A x).val) :
    IsZero ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x))) := by
  have hx := homotopy_isZero_of_unit_boundary A D x h dh
  have hR := (dgYoneda A D).onHomotopy.map_isZero hx
  have hQ := (moduleHomotopyToDerivedClosed A D).map_isZero hR
  exact hQ.of_iso ((moduleToHomotopyDerivedIso A D).app
    (ForgetEnrichment.of (Complex A) (representable A x))).symm

/-- S の代表加群は、明示的商の主導来圏で零。 -/
lemma quotientRepresentable_derived_isZero (S : Set D) (b : S) :
    IsZero ((moduleToDerived A (QuotientObject D S)).obj
      (ForgetEnrichment.of (Complex A) (representable A (⟨b.val⟩ : QuotientObject D S)))) :=
  representable_derived_isZero_of_unit_boundary A (QuotientObject D S) ⟨b.val⟩
    (epsilonElement A D S b) (differential_epsilonElement A D S b)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonContraction

/-! ## DerivedComparisonZeroModule（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonZeroModule.lean） -/

/-! # 長さ零段階と代表加群、および商への比較射

元の Hom と零段階の同型を、全次数自然な加群同型へ持ち上げる。
-/

@[expose] public section DerivedComparisonZeroModule
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
private lemma family_naturality_of_injective
    {M N T : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (j : ∀ x : Dᵒᵖ, N.obj x ⟶ T.obj x)
    (b : ∀ x : Dᵒᵖ, M.obj x ⟶ T.obj x)
    (hj : ∀ x i, Function.Injective ((j x).f i))
    (hfac : ∀ x, a x ≫ j x = b x)
    (hn : ∀ x y, N.map x y ≫ homPostcompose (N.obj x) (j y) =
      T.map x y ≫ homPrecompose (j x) (T.obj y))
    (hb : ∀ x y, M.map x y ≫ homPostcompose (M.obj x) (b y) =
      T.map x y ≫ homPrecompose (b x) (T.obj y)) (x y : Dᵒᵖ) :
    M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y) := by
  apply closedFamily_of_action A (M := M) (N := N) a
  intro x y p i k hik f t
  apply hj y k
  have hx := congrArg (fun g => g.f i t) (hfac x)
  have hy := congrArg (fun g => g.f k (moduleAction A M f t hik)) (hfac y)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at hx hy
  rw [hy, closedFamily_action A j hn, hx]
  exact closedFamily_action A b hb x y p i k hik f t

lemma lengthZeroModule_naturality (S : Set D) (z : D) (x y : Dᵒᵖ) :
    (representable A z).map x y ≫ homPostcompose (homObject A D x.unop z)
        (lengthZeroMap A D S y.unop z) =
      (lengthModule A D S z 0).map x y ≫ homPrecompose (lengthZeroMap A D S x.unop z)
        (lengthComplex A D S y.unop z 0) := by
  exact family_naturality_of_injective A D
    (M := representable A z) (N := lengthModule A D S z 0)
    (T := quotientRepresentableRestriction A D S z)
    (fun x => lengthZeroMap A D S x.unop z)
    (fun x => lengthInclusion A D S x.unop z 0)
    (fun x => originalHomInclusion A D S x.unop z)
    (fun _ _ => Subtype.val_injective)
    (fun x => lengthZeroMap_inclusion A D S x.unop z)
    (lengthModuleMap_inclusion A D S z 0)
    (representableRestriction_naturality A D (QuotientObject D S) (inclusion A D S) z) x y

/-- 元の代表加群から長さ零段階への実際の閉零射。 -/
def lengthZeroModuleMap (S : Set D) (z : D) :
    ForgetEnrichment.of (Complex A) (representable A z) ⟶
      ForgetEnrichment.of (Complex A) (lengthModule A D S z 0) :=
  moduleMorphismMk A D (fun x => lengthZeroMap A D S x.unop z)
    (lengthZeroModule_naturality A D S z)

@[simp] lemma lengthZeroModuleMap_eval (S : Set D) (z x : D) :
    (moduleEvaluation A D x).map (lengthZeroModuleMap A D S z) = lengthZeroMap A D S x z :=
  moduleMorphismMk_eval A D _ _ x

instance lengthZeroModuleMap_isIso (S : Set D) (z : D) :
    IsIso (lengthZeroModuleMap A D S z) :=
  moduleIsIso_of_evaluations A D _ (fun x => by
    rw [lengthZeroModuleMap_eval]
    infer_instance)

/-- 零段階は元の代表加群と、加群圏内で同型である。 -/
def lengthZeroModuleIso (S : Set D) (z : D) :
    ForgetEnrichment.of (Complex A) (representable A z) ≅
      ForgetEnrichment.of (Complex A) (lengthModule A D S z 0) :=
  asIso (lengthZeroModuleMap A D S z)

/-- 零段階の包含は、dg 関手の Hom 写像による代表加群の比較そのものである。 -/
@[reassoc] lemma lengthZeroModuleMap_inclusion (S : Set D) (z : D) :
    lengthZeroModuleMap A D S z ≫ lengthModuleInclusion A D S z 0 =
      representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, lengthZeroModuleMap_eval, lengthModuleInclusion_eval,
    representableRestrictionMap_eval]
  exact lengthZeroMap_inclusion A D S x z

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonZeroModule

/-! ## DerivedComparisonGenerators（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonGenerators.lean） -/

/-! # 空 path 包含による代表対象上の実際の導来比較

商への dg 関手、dg Yoneda、既存の主局所化の合成を使う。
tria(D) 全体への延長と Verdier 商上の完全忠実性は後続で扱う。
-/

@[expose] public section DerivedComparisonGenerators
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の H⁰ から商の導来圏へ、明示的包含と Yoneda で定まる比較。 -/
def derivedComparisonOnGenerators (S : Set D) :
    HomotopyCategory A D ⥤ DerivedModuleCategory A (QuotientObject D S) :=
  (inclusion A D S).onHomotopy ⋙ (dgYoneda A (QuotientObject D S)).onHomotopy ⋙
    moduleHomotopyToDerivedClosed A (QuotientObject D S)

def derivedComparisonOnGenerators_objIso (S : Set D) (x : D) :
    (derivedComparisonOnGenerators A D S).obj
        ((toHomotopy A D).obj (ForgetEnrichment.of (Complex A) x)) ≅
      (moduleToDerived A (QuotientObject D S)).obj
        (ForgetEnrichment.of (Complex A) (representable A (⟨x⟩ : QuotientObject D S))) :=
  (moduleToHomotopyDerivedIso A (QuotientObject D S)).app _

lemma derivedComparisonOnGenerators_finiteCell (S : Set D) (X : HomotopyCategory A D) :
    derivedFiniteCellOver A (QuotientObject D S) Set.univ
      ((derivedComparisonOnGenerators A D S).obj X) := by
  obtain ⟨x⟩ := X
  exact (derivedFiniteCellOver A (QuotientObject D S) Set.univ).prop_of_iso
    (derivedComparisonOnGenerators_objIso A D S x).symm
    ((moduleFiniteCellOver A (QuotientObject D S) Set.univ).prop_map_obj
      (moduleToDerived A (QuotientObject D S))
      (moduleFiniteCell_representable A (QuotientObject D S) ⟨x⟩))

/-- 比較の値域を U17a と同じ tria の対象型に制限する。 -/
def derivedComparisonGeneratorsToTria (S : Set D) :
    HomotopyCategory A D ⥤ TriaCategory A (QuotientObject D S) :=
  (derivedFiniteCellOver A (QuotientObject D S) Set.univ).lift
    (derivedComparisonOnGenerators A D S) (derivedComparisonOnGenerators_finiteCell A D S)

def derivedComparisonGeneratorsToTria_objIso (S : Set D) (x : D) :
    (derivedComparisonGeneratorsToTria A D S).obj
        ((toHomotopy A D).obj (ForgetEnrichment.of (Complex A) x)) ≅
      triaRepresentable A (QuotientObject D S) ⟨x⟩ :=
  (derivedFiniteCellOver A (QuotientObject D S) Set.univ).isoMk
    (derivedComparisonOnGenerators_objIso A D S x)

lemma derivedComparisonOnGenerators_kills (S : Set D) (b : S) :
    IsZero ((derivedComparisonOnGenerators A D S).obj
      ((toHomotopy A D).obj (ForgetEnrichment.of (Complex A) b.val))) :=
  (quotientRepresentable_derived_isZero A D S b).of_iso
    (derivedComparisonOnGenerators_objIso A D S b.val)

/-- 比較の代表像は、商側の tria 全体を三角生成する。retract を追加しない。 -/
lemma derivedComparisonGenerators_generate (S : Set D)
    (P : ObjectProperty (TriaCategory A (QuotientObject D S)))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hP : ∀ x : D, P ((derivedComparisonGeneratorsToTria A D S).obj
      ((toHomotopy A D).obj (ForgetEnrichment.of (Complex A) x))))
    (X : TriaCategory A (QuotientObject D S)) : P X := by
  have hle : triaImage A (QuotientObject D S) Set.univ ≤ P :=
    (triaImage_le_iff_generators A (QuotientObject D S) Set.univ P).2
      (fun x _ => P.prop_of_iso (derivedComparisonGeneratorsToTria_objIso A D S x.val)
        (hP x.val))
  exact hle X X.property

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonGenerators

/-! ## DerivedComparisonExtension（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonExtension.lean） -/

/-! # tria(D) 全体から明示的 dg 商の tria への比較

対象は加群の射影置換で扱う。局所 K-flat 下の Verdier 比較の完全忠実性は別段階。
-/

@[expose] public section DerivedComparisonExtension
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits ZeroObject Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 空 path の包含に沿う導来拡張を tria(D) 上で考える。 -/
def derivedComparisonFromTria (S : Set D) :
    TriaCategory A D ⥤ DerivedModuleCategory A (QuotientObject D S) :=
  triaInclusion A D ⋙ dgDerivedExtension A D (QuotientObject D S) (inclusion A D S)

lemma derivedComparisonFromTria_finiteCell (S : Set D) (X : TriaCategory A D) :
    derivedFiniteCellOver A (QuotientObject D S) Set.univ
      ((derivedComparisonFromTria A D S).obj X) :=
  graphDerivedExtension_derivedFiniteCell_mem A D (QuotientObject D S) (inclusion A D S)
    (derivedFiniteCellOver A (QuotientObject D S) Set.univ) Set.univ
    (fun x _ => (moduleFiniteCellOver A (QuotientObject D S) Set.univ).prop_map_obj
      (moduleToDerived A (QuotientObject D S))
      (moduleFiniteCell_representable A (QuotientObject D S) ⟨x⟩)) X.property

/-- tria の対象と射の全体に定義された比較関手。 -/
def derivedComparisonTria (S : Set D) : TriaCategory A D ⥤ TriaCategory A (QuotientObject D S) :=
  (derivedFiniteCellOver A (QuotientObject D S) Set.univ).lift
    (derivedComparisonFromTria A D S) (derivedComparisonFromTria_finiteCell A D S)

/-- 比較関手の代表対象上での計算。 -/
def derivedComparisonTria_representableIso (S : Set D) (x : D) :
    (derivedComparisonTria A D S).obj (triaRepresentable A D x) ≅
      triaRepresentable A (QuotientObject D S) ⟨x⟩ :=
  (derivedFiniteCellOver A (QuotientObject D S) Set.univ).isoMk
    (dgDerivedExtensionRepresentableIso A D (QuotientObject D S) (inclusion A D S) x)

/-- B の代表対象からの有限三角操作も、商側では全て零となる。 -/
lemma derivedComparisonFromTria_kills (S : Set D) (X : TriaCategory A D)
    (hX : triaImage A D S X) : IsZero ((derivedComparisonFromTria A D S).obj X) := by
  let P : ObjectProperty (DerivedModuleCategory A (QuotientObject D S)) := IsZero
  let : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h => h.of_iso e.symm⟩
  let : P.IsStableUnderShift ℤ :=
    ⟨fun n => ⟨fun _ h => (shiftFunctor _ n).map_isZero h⟩⟩
  let : P.IsTriangulated :=
    { exists_zero := ⟨0, isZero_zero _, isZero_zero _⟩
      ext₂' := fun T hT h₁ h₃ =>
        ⟨T.obj₂, T.isZero₂_of_isZero₁₃ hT h₁ h₃, ⟨Iso.refl _⟩⟩ }
  exact graphDerivedExtension_derivedFiniteCell_mem A D (QuotientObject D S) (inclusion A D S)
    P S (fun x hx => quotientRepresentable_derived_isZero A D S ⟨x, hx⟩) hX

/-- 値域を tria に制限しても、同じ零性を保つ。 -/
lemma derivedComparisonTria_kills (S : Set D) (X : TriaCategory A D)
    (hX : triaImage A D S X) : IsZero ((derivedComparisonTria A D S).obj X) := by
  rw [IsZero.iff_id_eq_zero]
  apply (triaInclusion A (QuotientObject D S)).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (derivedComparisonFromTria_kills A D S X hX).eq_of_src _ _

/-- この比較の代表対象の像は商側の tria を三角生成する。 -/
lemma derivedComparisonTria_generates (S : Set D)
    (P : ObjectProperty (TriaCategory A (QuotientObject D S)))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hP : ∀ x : D, P ((derivedComparisonTria A D S).obj (triaRepresentable A D x)))
    (X : TriaCategory A (QuotientObject D S)) : P X := by
  have hle := (triaImage_le_iff_generators A (QuotientObject D S) Set.univ P).2
    (fun x _ => P.prop_of_iso (derivedComparisonTria_representableIso A D S x.val) (hP x.val))
  exact hle X X.property

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonExtension

/-! ## DerivedComparisonRestriction（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonRestriction.lean） -/

/-! # dg 商の加群を制限したときの S 上の acyclic 性

商の任意の右 dg 加群は、指定収縮のある対象で acyclic である。
局所 K-flat 仮定が必要となる逆向きの本質像判定は、この零性と区別する。
-/

@[expose] public section DerivedComparisonRestriction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex Opposite
variable (A : Type u) [CommRing A]

lemma complex_acyclic_of_homotopy_isZero (K : Complex A)
    (hK : IsZero ((toHomotopy A (Complex A)).obj (ForgetEnrichment.of (Complex A) K))) :
    K.Acyclic := by
  have hQ : IsZero ((_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).obj K) :=
    (complexHomotopyComparison A).map_isZero hK
  intro n
  apply (exactAt_iff_isZero_homology K n).2
  have hH := (_root_.HomotopyCategory.homologyFunctor (ModuleCat.{u} A) (.up ℤ) n).map_isZero hQ
  exact hH.of_iso ((_root_.HomotopyCategory.homologyFunctorFactors
    (ModuleCat.{u} A) (.up ℤ) n).app K).symm

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 右加群は、商内で指定収縮を持つ各対象に acyclic 複体を割り当てる。 -/
lemma quotientModule_value_acyclic (S : Set D) (M : RightModule A (QuotientObject D S)) (b : S) :
    (M.obj (op (⟨b.val⟩ : QuotientObject D S))).Acyclic := by
  have hb : IsZero ((toHomotopy A (QuotientObject D S)ᵒᵖ).obj
      (ForgetEnrichment.of (Complex A) (op (⟨b.val⟩ : QuotientObject D S)))) :=
    homotopy_isZero_of_unit_boundary A (QuotientObject D S)ᵒᵖ (op ⟨b.val⟩)
      (epsilonElement A D S b) (differential_epsilonElement A D S b)
  exact complex_acyclic_of_homotopy_isZero A _ (M.toFunctor.onHomotopy.map_isZero hb)

/-- 閉零の制限関手の本質像は S 上で objectwise acyclic。 -/
lemma quotientModuleRestriction_value_acyclic (S : Set D)
    (M : ModuleCategory A (QuotientObject D S)) (b : S) :
    ((moduleEvaluation A D b.val).obj
      ((moduleRestriction A D (QuotientObject D S) (inclusion A D S).op).obj M)).Acyclic :=
  quotientModule_value_acyclic A D S (ForgetEnrichment.to (Complex A) M) b

/-- 導来制限の像も S 上の全ホモロジーが零である。置換や平坦性は不要。 -/
lemma quotientDerivedRestriction_homology_isZero (S : Set D)
    (X : DerivedModuleCategory A (QuotientObject D S)) (b : S) (n : ℤ) :
    IsZero ((moduleDerivedHomology A D b.val n).obj
      ((dgDerivedRestriction A D (QuotientObject D S) (inclusion A D S)).obj X)) := by
  obtain ⟨⟨M⟩⟩ := X
  have hR := congrArg (fun G => G.obj M)
    (dgDerivedRestriction_fac A D (QuotientObject D S) (inclusion A D S))
  change IsZero ((moduleDerivedHomology A D b.val n).obj
    ((moduleToDerived A (QuotientObject D S) ⋙
      dgDerivedRestriction A D (QuotientObject D S) (inclusion A D S)).obj M))
  rw [hR]
  let N := (moduleRestriction A D (QuotientObject D S) (inclusion A D S).op).obj M
  have hH := congrArg (fun G => G.obj N) (moduleDerivedHomology_fac A D b.val n)
  change IsZero ((moduleToDerived A D ⋙ moduleDerivedHomology A D b.val n).obj N)
  rw [hH]
  exact (quotientModuleRestriction_value_acyclic A D S M b n).isZero_homology

/-- S の代表加群から導来制限の像への射は零だけである。 -/
lemma quotientDerivedRestriction_representable_hom_subsingleton (S : Set D)
    (X : DerivedModuleCategory A (QuotientObject D S)) (b : S) :
    Subsingleton ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A b.val)) ⟶
        (dgDerivedRestriction A D (QuotientObject D S) (inclusion A D S)).obj X) := by
  have h : Subsingleton ((moduleDerivedHomology A D b.val 0).obj
      ((dgDerivedRestriction A D (QuotientObject D S) (inclusion A D S)).obj X)) :=
    ModuleCat.isZero_iff_subsingleton.mp (quotientDerivedRestriction_homology_isZero A D S X b 0)
  exact (moduleRepresentableDerivedHomEquiv A D b.val _).injective.subsingleton

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonRestriction

/-! ## DerivedComparisonTriangulated（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonTriangulated.lean） -/

/-! # 有限 cell の三角モデルによる dg 商比較と Verdier 因子化

局所 K-flat 性を要する完全忠実性に先立ち、実際の三角関手とその因子化を構成する。
-/

@[expose] public section DerivedComparisonTriangulated
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

local instance (S : Set D) : (dgModuleExtension A D (QuotientObject D S)
    (inclusion A D S)).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A D _ _
local instance (S : Set D) : (dgModuleExtension A D (QuotientObject D S)
    (inclusion A D S)).onHomotopy.CommShift ℤ :=
  dgModuleFunctorHomotopyCommShift A D _ _
local instance (S : Set D) : (dgModuleExtension A D (QuotientObject D S)
    (inclusion A D S)).onHomotopy.IsTriangulated :=
  dgModuleFunctorHomotopyIsTriangulated A D _ _

/-- 有限 cell の K(D) モデル上で graph tensor を使う比較。 -/
def quotientCellToDerived (S : Set D) :
    HomotopyFiniteCellCategoryOver A D Set.univ ⥤ DerivedModuleCategory A (QuotientObject D S) :=
  (homotopyFiniteCellOver A D Set.univ).ι ⋙
    (dgModuleExtension A D (QuotientObject D S) (inclusion A D S)).onHomotopy ⋙
      moduleHomotopyToDerivedClosed A (QuotientObject D S)

instance quotientCellToDerivedCommShift (S : Set D) :
    (quotientCellToDerived A D S).CommShift ℤ := by
  dsimp [quotientCellToDerived]
  infer_instance
instance quotientCellToDerivedIsTriangulated (S : Set D) :
    (quotientCellToDerived A D S).IsTriangulated := by
  dsimp [quotientCellToDerived]
  infer_instance

/-- 三角同値の逆関手を使うことで、tria 上に整合的な整数 shift と三角性を保つ。 -/
def quotientTriaToDerived (S : Set D) :
    TriaCategory A D ⥤ DerivedModuleCategory A (QuotientObject D S) :=
  (homotopyFiniteCellTriaEquivalence A D Set.univ).inverse ⋙ quotientCellToDerived A D S

instance quotientTriaToDerivedCommShift (S : Set D) :
    (quotientTriaToDerived A D S).CommShift ℤ := by
  dsimp [quotientTriaToDerived]
  infer_instance
instance quotientTriaToDerivedIsTriangulated (S : Set D) :
    (quotientTriaToDerived A D S).IsTriangulated := by
  dsimp [quotientTriaToDerived]
  infer_instance

lemma quotientCellToDerived_finiteCell (S : Set D)
    (X : HomotopyFiniteCellCategoryOver A D Set.univ) :
    derivedFiniteCellOver A (QuotientObject D S) Set.univ
      ((quotientCellToDerived A D S).obj X) := by
  obtain ⟨M, ⟨c⟩, ⟨e⟩⟩ := X.property
  let P := derivedFiniteCellOver A (QuotientObject D S) Set.univ
  have h := finiteCellCode_image_mem A D (QuotientObject D S)
    ((dgModuleExtension A D (QuotientObject D S) (inclusion A D S)).onClosed ⋙
      moduleToDerived A (QuotientObject D S))
    (graphExtension_cone_distinguished A D (QuotientObject D S) (inclusion A D S)) P
    (fun x _ => P.prop_of_iso ((moduleToDerived A (QuotientObject D S)).mapIso
      (dgModuleExtensionRepresentableIso A D (QuotientObject D S) (inclusion A D S) x)).symm
      ((moduleFiniteCellOver A (QuotientObject D S) Set.univ).prop_map_obj
        (moduleToDerived A (QuotientObject D S))
        (moduleFiniteCell_representable A (QuotientObject D S) ⟨x⟩))) c
  exact P.prop_of_iso
    ((dgExtensionHomotopyToDerived A D (QuotientObject D S) (inclusion A D S)).mapIso e)
    (P.prop_of_iso (dgExtensionHomotopyComputation A D (QuotientObject D S)
      (inclusion A D S) M).symm h)

/-- 明示的商への比較を、商側 tria に値を持つ三角関手として構成。 -/
def quotientTriaFunctor (S : Set D) : TriaCategory A D ⥤ TriaCategory A (QuotientObject D S) :=
  (derivedFiniteCellOver A (QuotientObject D S) Set.univ).lift (quotientTriaToDerived A D S)
    (fun _ => quotientCellToDerived_finiteCell A D S _)

instance quotientTriaFunctorCommShift (S : Set D) :
    (quotientTriaFunctor A D S).CommShift ℤ := by
  dsimp [quotientTriaFunctor]
  infer_instance
instance quotientTriaFunctorIsTriangulated (S : Set D) :
    (quotientTriaFunctor A D S).IsTriangulated := by
  dsimp [quotientTriaFunctor]
  infer_instance

/-- 三角モデルにおける代表対象。 -/
def homotopyCellRepresentable (x : D) : HomotopyFiniteCellCategoryOver A D Set.univ :=
  ⟨(moduleToHomotopy A D).obj (ForgetEnrichment.of (Complex A) (representable A x)),
    (moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToHomotopy A D)
      (moduleFiniteCell_representable A D x)⟩

def homotopyCellRepresentableIso (x : D) :
    (homotopyFiniteCellTriaEquivalence A D Set.univ).functor.obj (homotopyCellRepresentable A D x) ≅
      triaRepresentable A D x :=
  (derivedFiniteCellOver A D Set.univ).isoMk ((moduleToHomotopyDerivedIso A D).app _)

/-- 実際の三角比較も、空 path の像の代表加群として計算できる。 -/
def quotientTriaFunctor_representableIso (S : Set D) (x : D) :
    (quotientTriaFunctor A D S).obj (triaRepresentable A D x) ≅
      triaRepresentable A (QuotientObject D S) ⟨x⟩ := by
  let e := homotopyFiniteCellTriaEquivalence A D Set.univ
  let t := e.inverse.mapIso (homotopyCellRepresentableIso A D x).symm ≪≫
    (e.unitIso.app (homotopyCellRepresentable A D x)).symm
  exact (derivedFiniteCellOver A (QuotientObject D S) Set.univ).isoMk
    ((quotientCellToDerived A D S).mapIso t ≪≫
      dgExtensionHomotopyComputation A D (QuotientObject D S) (inclusion A D S) _ ≪≫
      (moduleToDerived A (QuotientObject D S)).mapIso
        (dgModuleExtensionRepresentableIso A D (QuotientObject D S) (inclusion A D S) x))

lemma quotientTriaFunctor_kills (S : Set D) :
    triaImage A D S ≤ triangulatedKernel (quotientTriaFunctor A D S) := by
  refine (triaImage_le_iff_generators A D S
    (triangulatedKernel (quotientTriaFunctor A D S))).2 ?_
  intro x hx
  rw [triangulatedKernel, IsZero.iff_id_eq_zero]
  apply (triaInclusion A (QuotientObject D S)).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  have h := (quotientRepresentable_derived_isZero A D S ⟨x, hx⟩).of_iso
    ((triaInclusion A (QuotientObject D S)).mapIso (quotientTriaFunctor_representableIso A D S x))
  exact h.eq_of_src _ _

/-- tria(S) の cone を持つ Verdier 分母は、実際の比較で可逆になる。 -/
lemma quotientTriaFunctor_inverts (S : Set D) :
    (triaImage A D S).trW.IsInvertedBy (quotientTriaFunctor A D S) := by
  intro X Y f hf
  exact (triangulatedKernel_trW_iff (quotientTriaFunctor A D S) f).1
    ((triaImage A D S).trW_monotone (quotientTriaFunctor_kills A D S) _ hf)

/-- 局所 K-flat 比較で完全忠実性を証明すべき、指定された実際の関手。 -/
def quotientVerdierComparison (S : Set D) :
    TriaQuotient A D S ⥤ TriaCategory A (QuotientObject D S) :=
  Localization.lift (quotientTriaFunctor A D S) (quotientTriaFunctor_inverts A D S)
    (triaQuotient A D S)

/-- U17a の指定局所化と実際の三角比較との因子化同型。 -/
def quotientVerdierComparisonFactors (S : Set D) :
    triaQuotient A D S ⋙ quotientVerdierComparison A D S ≅ quotientTriaFunctor A D S :=
  Localization.fac (quotientTriaFunctor A D S) (quotientTriaFunctor_inverts A D S)
    (triaQuotient A D S)

instance quotientVerdierComparisonLifting (S : Set D) :
    Localization.Lifting (triaQuotient A D S) (triaImage A D S).trW
      (quotientTriaFunctor A D S) (quotientVerdierComparison A D S) :=
  Localization.liftingLift (quotientTriaFunctor A D S) (quotientTriaFunctor_inverts A D S)
    (triaQuotient A D S)

instance quotientVerdierComparisonCommShift (S : Set D) :
    (quotientVerdierComparison A D S).CommShift ℤ :=
  Functor.commShiftOfLocalization (triaQuotient A D S) (triaImage A D S).trW ℤ
    (quotientTriaFunctor A D S) (quotientVerdierComparison A D S)

instance quotientVerdierComparisonFactorsCommShift (S : Set D) :
    NatTrans.CommShift (quotientVerdierComparisonFactors A D S).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization (triaQuotient A D S) (triaImage A D S).trW ℤ
    (quotientTriaFunctor A D S) (quotientVerdierComparison A D S)

instance quotientVerdierComparisonIsTriangulated (S : Set D) :
    (quotientVerdierComparison A D S).IsTriangulated := by
  have : (triaQuotient A D S).mapArrow.EssSurj :=
    Localization.essSurj_mapArrow (triaQuotient A D S) (triaImage A D S).trW
  exact Functor.isTriangulated_of_precomp_iso (quotientVerdierComparisonFactors A D S)

/-- 指定した局所化の代表対象について、比較後の代表加群を計算する。 -/
def quotientVerdierComparison_representableIso (S : Set D) (x : D) :
    (quotientVerdierComparison A D S).obj ((triaQuotient A D S).obj (triaRepresentable A D x)) ≅
      triaRepresentable A (QuotientObject D S) ⟨x⟩ :=
  (quotientVerdierComparisonFactors A D S).app (triaRepresentable A D x) ≪≫
    quotientTriaFunctor_representableIso A D S x

/-- 完全性が得られれば、本質像の三角閉性と代表生成性から本質的全射性が従う。 -/
instance quotientVerdierComparisonEssSurj (S : Set D) [(quotientVerdierComparison A D S).Full] :
    (quotientVerdierComparison A D S).EssSurj where
  mem_essImage X := by
    have hle := (triaImage_le_iff_generators A (QuotientObject D S) Set.univ
      (quotientVerdierComparison A D S).essImage).2
      (fun x _ => ⟨(triaQuotient A D S).obj (triaRepresentable A D x.val),
        ⟨quotientVerdierComparison_representableIso A D S x.val⟩⟩)
    exact hle X X.property

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonTriangulated

/-! ## DerivedComparisonPathFlatness（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonPathFlatness.lean） -/

/-! # 片側局所 K-flat 仮定と path の係数複体

内部微分だけを持つ path 項を扱う。最終微分の長さ filtration は別工程である。
-/

@[expose] public section DerivedComparisonPathFlatness
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 入る Hom が K-flat なら、殺す対象を終点とする全ての内部 path 項が K-flat。 -/
lemma term_kFlat_into {S : Set D} (h : homIntoKFlat A D S)
    (w : Word S) (x : D) (b : S) : complexKFlat A (term A D w x b.val) := by
  induction w generalizing x with
  | nil => exact h x b
  | cons c w ih =>
    exact complexKFlat_tensor A (h x c)
      (complexKFlat_tensor A (complexSphere_kFlat A (-1)) (ih c.val))

/-- 出る Hom が K-flat なら、殺す対象を始点とする全ての内部 path 項が K-flat。 -/
lemma term_kFlat_outOf {S : Set D} (h : homOutOfKFlat A D S)
    (w : Word S) (b : S) (y : D) : complexKFlat A (term A D w b.val y) := by
  induction w generalizing b with
  | nil => exact h b y
  | cons c w ih =>
    exact complexKFlat_tensor A (h b c.val)
      (complexKFlat_tensor A (complexSphere_kFlat A (-1)) (ih c))

/-- 最後の Hom(b,y) を除き、最後の ε は残した path の前方係数。 -/
def pathPrefixWeight {S : Set D} : Word S → D → S → Complex A
  | [], x, b => homObject A D x b.val ⊗ epsilonComplex A
  | c :: w, x, b => homObject A D x c.val ⊗ (epsilonComplex A ⊗ pathPrefixWeight w c.val b)

/-- 最初の Hom(x,b) を除き、最初の ε は残した path の後方係数。 -/
def pathSuffixWeight {S : Set D} (w : Word S) (b : S) (y : D) : Complex A :=
  epsilonComplex A ⊗ term A D w b.val y

/-- path 添字を保持し、最後の Hom だけを右 tensor 因子に分離する。 -/
def termSnocWeightIso {S : Set D} (w : Word S) (x : D) (b : S) (y : D) :
    term A D (w ++ [b]) x y ≅ pathPrefixWeight A D w x b ⊗ homObject A D b.val y := by
  induction w generalizing x with
  | nil => exact (α_ (homObject A D x b.val) (epsilonComplex A) (homObject A D b.val y)).symm
  | cons c w ih =>
    exact (Iso.refl (homObject A D x c.val) ⊗ᵢ
      (Iso.refl (epsilonComplex A) ⊗ᵢ ih c.val)) ≪≫
      (Iso.refl (homObject A D x c.val) ⊗ᵢ
        (α_ (epsilonComplex A) (pathPrefixWeight A D w c.val b) (homObject A D b.val y)).symm) ≪≫
      (α_ (homObject A D x c.val) (epsilonComplex A ⊗ pathPrefixWeight A D w c.val b)
        (homObject A D b.val y)).symm

lemma pathPrefixWeight_kFlat {S : Set D} (h : homIntoKFlat A D S)
    (w : Word S) (x : D) (b : S) : complexKFlat A (pathPrefixWeight A D w x b) := by
  induction w generalizing x with
  | nil => exact complexKFlat_tensor A (h x b) (complexSphere_kFlat A (-1))
  | cons c w ih =>
    exact complexKFlat_tensor A (h x c)
      (complexKFlat_tensor A (complexSphere_kFlat A (-1)) (ih c.val))

lemma pathSuffixWeight_kFlat {S : Set D} (h : homOutOfKFlat A D S)
    (w : Word S) (b : S) (y : D) : complexKFlat A (pathSuffixWeight A D w b y) :=
  complexKFlat_tensor A (complexSphere_kFlat A (-1)) (term_kFlat_outOf A D h w b y)

/-- 前方係数との tensor は、任意の非有界 acyclic 複体を acyclic に保つ。 -/
lemma pathPrefixWeight_tensor_acyclic {S : Set D} (h : homIntoKFlat A D S)
    (w : Word S) (x : D) (b : S) (K : Complex A) (hK : K.Acyclic) :
    (pathPrefixWeight A D w x b ⊗ K).Acyclic :=
  pathPrefixWeight_kFlat A D h w x b K hK

/-- 前方係数との tensor は、末尾の任意の擬同型を保つ。末尾の平坦性は要求しない。 -/
lemma pathPrefixWeight_tensor_quasiIso {S : Set D} (h : homIntoKFlat A D S)
    (w : Word S) (x : D) (b : S) {K L : Complex A} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (cochainTensorMap (𝟙 (pathPrefixWeight A D w x b)) f) :=
  complexKFlat_quasiIso_right A (pathPrefixWeight_kFlat A D h w x b) f

/-- 後方係数との tensor は、先頭の任意の擬同型を保つ。先頭の平坦性は要求しない。 -/
lemma pathSuffixWeight_tensor_quasiIso {S : Set D} (h : homOutOfKFlat A D S)
    (w : Word S) (b : S) (y : D) {K L : Complex A} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (cochainTensorMap f (𝟙 (pathSuffixWeight A D w b y))) :=
  complexKFlat_quasiIso_left A (pathSuffixWeight_kFlat A D h w b y) f

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonPathFlatness

/-! ## DerivedComparisonPathModule（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonPathModule.lean） -/

/-! # 内部 path 項の右 dg 加群構造

正の path は代表加群への右 tensor として構成する。最終微分の ε 消去は含めない。
-/

@[expose] public section DerivedComparisonPathModule
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex Opposite
variable {A : Type u} [CommRing A]

/-- 右 tensor の豊穣関手。 -/
def pathTensorRightDG (K : Complex A) : DGFunctor A (Complex A) (Complex A) where
  obj P := P ⊗ K
  map P Q := tensorRightHom K P Q
  map_id P := by
    apply (unitCycleEquiv _).injective
    apply Subtype.ext
    change (cycleFromUnit _ (identity P ≫ tensorRightHom K P P)).val =
      (cycleFromUnit _ (identity (P ⊗ K))).val
    rw [cycleFromUnit_postcomp, identity, identity, cycleFromUnit_unitFromCycle,
      cycleFromUnit_unitFromCycle]
    change (tensorRightHom K P P).f 0 (Cochain.ofHom (𝟙 P)) =
      Cochain.ofHom (𝟙 (P ⊗ K))
    rw [tensorRightHom_ofHom, id_whiskerRight]
  map_comp P Q T := by
    apply tensorHom_ext
    intro p q m hm
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro f g
    change (tensorRightHom K P T).f m
      ((enrichedComposition P Q T).f m
        (ιTensorObj (homComplex A P Q) (homComplex A Q T) p q m hm (f ⊗ₜ[A] g))) =
      (enrichedComposition _ _ _).f m
        ((tensorRightHom K P Q ⊗ₘ tensorRightHom K Q T).f m
          (ιTensorObj (homComplex A P Q) (homComplex A Q T) p q m hm (f ⊗ₜ[A] g)))
    rw [tensorMap_apply, enrichedComposition_apply, enrichedComposition_apply,
      chain_units_smul, tensorRightHom_cochain_comp]

/-- 全次数の右 tensor 作用の tensor 転置。 -/
lemma pathTensorRight_uncurry {H P Q : Complex A} (K : Complex A)
    (f : H ⟶ homComplex A P Q) :
    uncurryRight (f ≫ tensorRightHom K P Q) =
      (α_ H P K).inv ≫ (uncurryRight f ▷ K) := by
  apply rightTriple_ext
  intro i j k n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a t
  induction t using TensorProduct.inductionOn with
  | tmul b c =>
    change (uncurryRight (f ≫ tensorRightHom K P Q)).f n
      (ιTensorObj H (P ⊗ K) i (j + k) n hn
        (a ⊗ₜ[A] ιTensorObj P K j k (j + k) rfl (b ⊗ₜ[A] c))) = _
    rw [uncurryRight_apply]
    change ((tensorRightHom K P Q).f i (f.f i a)).v (j + k) n (by omega)
      (ιTensorObj P K j k (j + k) rfl (b ⊗ₜ[A] c)) = _
    rw [tensorRightHom_apply_of_sum K P Q i j k (j + k) (i + j) n rfl (by omega) (by omega)]
    change _ = (uncurryRight f ▷ K).f n ((α_ H P K).inv.f n
      (ιTensorObj H (P ⊗ K) i (j + k) n hn
        (a ⊗ₜ[A] ιTensorObj P K j k (j + k) rfl (b ⊗ₜ[A] c))))
    rw [associator_inv_apply, whiskerRight_apply, uncurryRight_apply]
  | add t t' ht ht' =>
    simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) ht ht'

lemma pathTensorRight_swap (K P Q : Complex A) :
    tensorRightHom K P Q ≫ homPostcompose (P ⊗ K) (signedSwap Q K).hom =
      tensorLeftHom K P Q ≫ homPrecompose (signedSwap P K).hom (K ⊗ Q) := by
  have hs : (signedSwap K Q).hom ≫ (signedSwap Q K).hom = 𝟙 (K ⊗ Q) :=
    SymmetricCategory.symmetry K Q
  change (tensorLeftHom K P Q ≫ homPrecompose (signedSwap P K).hom (K ⊗ Q) ≫
    (homFunctor (P ⊗ K)).map (signedSwap K Q).hom) ≫
      (homFunctor (P ⊗ K)).map (signedSwap Q K).hom = _
  rw [Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp, hs,
    CategoryTheory.Functor.map_id]
  change tensorLeftHom K P Q ≫ homPrecompose (signedSwap P K).hom (K ⊗ Q) ≫
    𝟙 (homComplex A (P ⊗ K) (K ⊗ Q)) = _
  rw [Category.comp_id]

variable (A) (D : Type v) [DGCategory A D]

/-- 元の圏を始点方向に動かす内部 path 項の右 dg 加群。 -/
def pathModule {S : Set D} (w : Word S) (z : D) : RightModule A D :=
  match w with
  | [] => representable A z
  | b :: w => (representable A b.val).toFunctor.comp
      (pathTensorRightDG (pathSuffixWeight A D w b z))

/-- 加群の値と元の path 項の明示的な複体同型。 -/
def pathModuleValueIso {S : Set D} (w : Word S) (z : D) (x : Dᵒᵖ) :
    (pathModule A D w z).obj x ≅ term A D w x.unop z := by
  cases w <;> exact Iso.refl _

/-- path 加群の作用は、指定した先頭 Hom の合成そのものである。 -/
lemma pathModule_action {S : Set D} (w : Word S) (z : D) (x y : Dᵒᵖ) :
    ((x ⟶[Complex A] y) ◁ (pathModuleValueIso A D w z x).inv) ≫
      moduleActionChain A (pathModule A D w z) x y ≫
        (pathModuleValueIso A D w z y).hom =
      prependMap A D w y.unop x.unop z := by
  cases w with
  | nil =>
    change (homObject A D y.unop x.unop ◁ 𝟙 (homObject A D x.unop z)) ≫
      uncurryRight (curryRight (eComp (Complex A) y.unop x.unop z)) ≫
        𝟙 (homObject A D y.unop z) = _
    rw [whiskerLeft_id, Category.id_comp, Category.comp_id, uncurryRight_curryRight]
    rfl
  | cons b w =>
    change (homObject A D y.unop x.unop ◁
      𝟙 (homObject A D x.unop b.val ⊗ pathSuffixWeight A D w b z)) ≫
      uncurryRight (representableMap A b.val x y ≫
      tensorRightHom (pathSuffixWeight A D w b z)
        (homObject A D x.unop b.val) (homObject A D y.unop b.val)) ≫
          𝟙 (homObject A D y.unop b.val ⊗ pathSuffixWeight A D w b z) = _
    rw [whiskerLeft_id, Category.id_comp, Category.comp_id]
    rw [pathTensorRight_uncurry]
    change (α_ _ _ _).inv ≫ (uncurryRight (curryRight
      (eComp (Complex A) y.unop x.unop b.val)) ▷ _) = _
    rw [uncurryRight_curryRight]
    rfl

lemma pathModule_action_value {S : Set D} (w : Word S) (z : D) (x y : Dᵒᵖ) :
    moduleActionChain A (pathModule A D w z) x y ≫ (pathModuleValueIso A D w z y).hom =
      ((x ⟶[Complex A] y) ◁ (pathModuleValueIso A D w z x).hom) ≫
        prependMap A D w y.unop x.unop z := by
  have h := congrArg (fun f => ((x ⟶[Complex A] y) ◁
    (pathModuleValueIso A D w z x).hom) ≫ f) (pathModule_action A D w z x y)
  simpa only [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    Iso.hom_inv_id, whiskerLeft_id, Category.id_comp] using h

variable [Small.{u} D]

/-- 正の path は、先頭の殺す対象における自由右加群と同型。 -/
def pathModuleFreeIso {S : Set D} (b : S) (w : Word S) (z : D) :
    ForgetEnrichment.of (Complex A) (pathModule A D (b :: w) z) ≅
      (freeAt b.val).obj (pathSuffixWeight A D w b z) :=
  moduleIsoMk A D
    (fun x => signedSwap (homObject A D x.unop b.val) (pathSuffixWeight A D w b z)) (by
      intro x y
      change (representableMap A b.val x y ≫ tensorRightHom _ _ _) ≫
        homPostcompose _ (signedSwap _ _).hom =
          (representableMap A b.val x y ≫ tensorLeftHom _ _ _) ≫
            homPrecompose (signedSwap _ _).hom _
      rw [Category.assoc, pathTensorRight_swap, Category.assoc])

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonPathModule

/-! ## DerivedComparisonLocalObjects（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonLocalObjects.lean） -/

/-! # 商の導来制限の像は指定有限 cell に対して局所的

代表加群上の零性から全ての指定有限 cell 上の右直交性へ運ぶ。
-/

@[expose] public section DerivedComparisonLocalObjects
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 商の任意の導来加群の制限は、S で生成される全有限 cell に右直交する。 -/
lemma quotientDerivedRestriction_rightOrthogonal (S : Set D)
    (X : DerivedModuleCategory A (QuotientObject D S)) :
    (derivedFiniteCellOver A D S).rightOrthogonal
      ((dgDerivedRestriction A D (QuotientObject D S) (inclusion A D S)).obj X) := by
  let R := dgDerivedRestriction A D (QuotientObject D S) (inclusion A D S)
  let : R.CommShift ℤ := dgDerivedRestrictionCommShift A D _ _
  let : R.essImage.IsStableUnderShift ℤ := {
    isStableUnderShiftBy := fun n => {
      le_shift := by
        rintro Y ⟨Z, ⟨e⟩⟩
        exact ⟨Z⟦n⟧, ⟨(R.commShiftIso n).app Z ≪≫ (shiftFunctor _ n).mapIso e⟩⟩ } }
  have hle : derivedFiniteCellOver A D S ≤ R.essImage.leftOrthogonal :=
    (derivedFiniteCellOver_le_iff_generators A D R.essImage.leftOrthogonal S).2 (by
      intro b hb Y f hY
      obtain ⟨Z, ⟨e⟩⟩ := hY
      apply (cancel_mono e.inv).1
      rw [zero_comp]
      exact (quotientDerivedRestriction_representable_hom_subsingleton A D S Z ⟨b, hb⟩).elim _ _)
  intro Y f hY
  exact hle Y hY f ⟨X, ⟨Iso.refl _⟩⟩

/-- 制限の像への Hom は、指定有限 cell の cone を持つ射の前置で変わらない。 -/
lemma quotientDerivedRestriction_isLocal (S : Set D)
    (X : DerivedModuleCategory A (QuotientObject D S)) :
    (derivedFiniteCellOver A D S).trW.isLocal
      ((dgDerivedRestriction A D (QuotientObject D S) (inclusion A D S)).obj X) := by
  rw [ObjectProperty.isLocal_trW]
  exact quotientDerivedRestriction_rightOrthogonal A D S X

/-- tria(D) に制限した Hom も、U17a の指定 Verdier 分母の前置で不変。 -/
lemma quotientDerivedRestriction_tria_precomp_bijective (S : Set D)
    (X : DerivedModuleCategory A (QuotientObject D S))
    {M N : TriaCategory A D} (s : M ⟶ N) (hs : (triaImage A D S).trW s) :
    Function.Bijective (fun f : (triaInclusion A D).obj N ⟶
      (dgDerivedRestriction A D (QuotientObject D S) (inclusion A D S)).obj X =>
        (triaInclusion A D).map s ≫ f) :=
  quotientDerivedRestriction_isLocal A D S X _
    (((derivedFiniteCellOver A D S).inverseImage_trW_iff (triaInclusion A D) s).1 hs)

/-- 実際の制限代表加群の導来像も、置換なしで局所対象になる。 -/
lemma quotientRepresentableRestriction_isLocal (S : Set D) (z : D) :
    (derivedFiniteCellOver A D S).trW.isLocal ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z))) := by
  let M : ModuleCategory A (QuotientObject D S) :=
    ForgetEnrichment.of (Complex A) (representable A (⟨z⟩ : QuotientObject D S))
  have h := quotientDerivedRestriction_isLocal A D S
    ((moduleToDerived A (QuotientObject D S)).obj M)
  have he := congrArg (fun F => F.obj M)
    (dgDerivedRestriction_fac A D (QuotientObject D S) (inclusion A D S))
  change (dgDerivedRestriction A D (QuotientObject D S) (inclusion A D S)).obj
      ((moduleToDerived A (QuotientObject D S)).obj M) = _ at he
  rw [he] at h
  exact h

lemma quotientRepresentableRestriction_tria_precomp_bijective (S : Set D) (z : D)
    {M N : TriaCategory A D} (s : M ⟶ N) (hs : (triaImage A D S).trW s) :
    Function.Bijective (fun f : (triaInclusion A D).obj N ⟶
      (moduleToDerived A D).obj
        (ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z)) =>
          (triaInclusion A D).map s ≫ f) :=
  quotientRepresentableRestriction_isLocal A D S z _
    (((derivedFiniteCellOver A D S).inverseImage_trW_iff (triaInclusion A D) s).1 hs)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonLocalObjects

/-! ## DerivedComparisonHomPresheaf（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonHomPresheaf.lean） -/

/-! # 制限代表加群への Hom を指定 Verdier 商へ降ろす -/

@[expose] public section DerivedComparisonHomPresheaf
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 商の制限代表加群への導来 Hom の反変関手。 -/
def quotientRestrictionHomPresheaf (S : Set D) (z : D) :
    (TriaCategory A D)ᵒᵖ ⥤ Type (max (u + 1) v) :=
  (triaInclusion A D).op ⋙ yoneda.obj ((moduleToDerived A D).obj
    (ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z)))

lemma quotientRestrictionHomPresheaf_inverts (S : Set D) (z : D) :
    (triaImage A D S).trW.op.IsInvertedBy (quotientRestrictionHomPresheaf A D S z) := by
  intro X Y f hf
  apply (CategoryTheory.isIso_iff_bijective _).2
  exact quotientRepresentableRestriction_tria_precomp_bijective A D S z f.unop hf

/-- U17a の指定 Verdier 商上に降りた、制限代表加群への Hom。 -/
def quotientRestrictionLocalizedHom (S : Set D) (z : D) :
    (TriaQuotient A D S)ᵒᵖ ⥤ Type (max (u + 1) v) :=
  Localization.lift (quotientRestrictionHomPresheaf A D S z)
    (quotientRestrictionHomPresheaf_inverts A D S z) (triaQuotient A D S).op

/-- 元の tria 上への引き戻しは、元の導来 Hom そのもの。 -/
def quotientRestrictionLocalizedHomFactors (S : Set D) (z : D) :
    (triaQuotient A D S).op ⋙ quotientRestrictionLocalizedHom A D S z ≅
      quotientRestrictionHomPresheaf A D S z :=
  Localization.fac (quotientRestrictionHomPresheaf A D S z)
    (quotientRestrictionHomPresheaf_inverts A D S z) (triaQuotient A D S).op

/-- 商上の Hom 反変関手の値と実際の導来 Hom の計算同値。 -/
def quotientRestrictionLocalizedHomEquiv (S : Set D) (z : D) (X : TriaCategory A D) :
    (quotientRestrictionLocalizedHom A D S z).obj (op ((triaQuotient A D S).obj X)) ≃
      ((triaInclusion A D).obj X ⟶ (moduleToDerived A D).obj
        (ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z))) :=
  ((quotientRestrictionLocalizedHomFactors A D S z).app (op X)).toEquiv

/-- 計算同値は、元の tria の射に沿う前置と可換。 -/
lemma quotientRestrictionLocalizedHomEquiv_naturality (S : Set D) (z : D)
    {M N : TriaCategory A D} (s : M ⟶ N)
    (t : (quotientRestrictionLocalizedHom A D S z).obj
      (op ((triaQuotient A D S).obj N))) :
    quotientRestrictionLocalizedHomEquiv A D S z M
      ((quotientRestrictionLocalizedHom A D S z).map ((triaQuotient A D S).map s).op t) =
        (triaInclusion A D).map s ≫ quotientRestrictionLocalizedHomEquiv A D S z N t := by
  exact congrArg (fun k => k t)
    ((quotientRestrictionLocalizedHomFactors A D S z).hom.naturality s.op)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonHomPresheaf

/-! ## DerivedComparisonGradedTensor（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonGradedTensor.lean） -/

/-! # 固定長 path の両端分解と片側 K-flat 係数 -/

@[expose] public section DerivedComparisonGradedTensor
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex

/-- 長さを指定した word。元の word と長さの証拠をそのまま保持する。 -/
abbrev LengthWord {D : Type v} (S : Set D) (n : ℕ) := {w : Word S // w.length = n}

def consLengthWordEquiv {D : Type v} (S : Set D) (n : ℕ) :
    S × LengthWord S n ≃ LengthWord S (n + 1) :=
  Equiv.ofBijective (fun p => ⟨p.1 :: p.2.val, by simp only [List.length_cons, p.2.property]⟩)
    (by
      constructor
      · rintro ⟨b, w⟩ ⟨c, z⟩ h
        have h' := List.cons.inj (congrArg Subtype.val h)
        exact Prod.ext h'.1 (Subtype.ext h'.2)
      · rintro ⟨w, hw⟩
        cases w with
        | nil => simp only [List.length_nil] at hw; omega
        | cons b w =>
          exact ⟨(b, ⟨w, by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hw⟩),
            Subtype.ext rfl⟩)

def reverseLengthWordEquiv {D : Type v} (S : Set D) (n : ℕ) : LengthWord S n ≃ LengthWord S n where
  toFun w := ⟨w.val.reverse, by simpa only [List.length_reverse] using w.property⟩
  invFun w := ⟨w.val.reverse, by simpa only [List.length_reverse] using w.property⟩
  left_inv w := Subtype.ext (List.reverse_reverse w.val)
  right_inv w := Subtype.ext (List.reverse_reverse w.val)

/-- 最後の指定対象と、それ以前の word を取り出す添字同値。 -/
def snocLengthWordEquiv {D : Type v} (S : Set D) (n : ℕ) :
    S × LengthWord S n ≃ LengthWord S (n + 1) :=
  ((Equiv.prodCongr (Equiv.refl S) (reverseLengthWordEquiv S n)).trans
    (consLengthWordEquiv S n)).trans (reverseLengthWordEquiv S (n + 1))

lemma snocLengthWordEquiv_val {D : Type v} (S : Set D) (n : ℕ) (b : S) (w : LengthWord S n) :
    (snocLengthWordEquiv S n (b, w)).val = w.val ++ [b] := by
  change (b :: w.val.reverse).reverse = w.val ++ [b]
  rw [List.reverse_cons, List.reverse_reverse]

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- Hom(x,b) を先頭に残し、残りを後方係数とする固定長直和の同型。 -/
def fixedLengthSuffixIso (S : Set D) (x y : D) (n : ℕ) :
    fixedLengthHom A D S x y (n + 1) ≅
      ∐ (fun p : S × LengthWord S n => homObject A D x p.1.val ⊗
        pathSuffixWeight A D p.2.val p.1 y) :=
  (Sigma.whiskerEquiv (consLengthWordEquiv S n) (fun _ => Iso.refl _)).symm

/-- Hom(b,y) を末尾に残し、残りを前方係数とする固定長直和の同型。 -/
def fixedLengthPrefixIso (S : Set D) (x y : D) (n : ℕ) :
    fixedLengthHom A D S x y (n + 1) ≅
      ∐ (fun p : S × LengthWord S n => pathPrefixWeight A D p.2.val x p.1 ⊗
        homObject A D p.1.val y) :=
  (Sigma.whiskerEquiv (snocLengthWordEquiv S n) (fun p => by
    change term A D (snocLengthWordEquiv S n p).val x y ≅ _
    rw [snocLengthWordEquiv_val]
    exact termSnocWeightIso A D p.2.val x p.1 y)).symm

/-- 随伴次数部分の前方係数による実際の tensor 直和表示。 -/
def lengthGradedPrefixIso (S : Set D) (x y : D) (n : ℕ) :
    cokernel (lengthMap A D S x y (Nat.le_succ n)) ≅
      ∐ (fun p : S × LengthWord S n => pathPrefixWeight A D p.2.val x p.1 ⊗
        homObject A D p.1.val y) :=
  lengthGradedIso A D S x y n ≪≫ fixedLengthPrefixIso A D S x y n

/-- 随伴次数部分の後方係数による実際の tensor 直和表示。 -/
def lengthGradedSuffixIso (S : Set D) (x y : D) (n : ℕ) :
    cokernel (lengthMap A D S x y (Nat.le_succ n)) ≅
      ∐ (fun p : S × LengthWord S n => homObject A D x p.1.val ⊗
        pathSuffixWeight A D p.2.val p.1 y) :=
  lengthGradedIso A D S x y n ≪≫ fixedLengthSuffixIso A D S x y n

/-- u-small な添字族の余積は非有界 acyclic 複体を保つ。 -/
lemma pathCoproduct_acyclic {I : Type v} [Small.{u} I] (F : I → Complex A)
    (hF : ∀ i, (F i).Acyclic) : (∐ F).Acyclic := by
  have : HasExactColimitsOfShape (Discrete I) (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (Discrete.equivalence (equivShrink I).symm)
  exact complex_colimit_acyclic A (Discrete.functor F) (fun i => hF i.as)

/-- 入る側の K-flat 仮定の下で、S から y への Hom が acyclic なら全ての正の層が acyclic。 -/
lemma fixedLengthHom_acyclic_into (S : Set D) (h : homIntoKFlat A D S) (x y : D)
    (hy : ∀ b : S, (homObject A D b.val y).Acyclic) (n : ℕ) :
    (fixedLengthHom A D S x y (n + 1)).Acyclic := by
  have hc := pathCoproduct_acyclic A
    (fun p : S × LengthWord S n => pathPrefixWeight A D p.2.val x p.1 ⊗ homObject A D p.1.val y)
    (fun p => pathPrefixWeight_kFlat A D h p.2.val x p.1 _ (hy p.1))
  exact cochainAcyclic_of_iso hc (fixedLengthPrefixIso A D S x y n).symm

/-- 出る側の K-flat 仮定の下で、x から S への Hom が acyclic なら全ての正の層が acyclic。 -/
lemma fixedLengthHom_acyclic_outOf (S : Set D) (h : homOutOfKFlat A D S) (x y : D)
    (hx : ∀ b : S, (homObject A D x b.val).Acyclic) (n : ℕ) :
    (fixedLengthHom A D S x y (n + 1)).Acyclic := by
  have hc := pathCoproduct_acyclic A
    (fun p : S × LengthWord S n => homObject A D x p.1.val ⊗ pathSuffixWeight A D p.2.val p.1 y)
    (fun p => cochainAcyclic_of_iso (pathSuffixWeight_kFlat A D h p.2.val p.1 y _ (hx p.1))
      (cochainTensorSymmetry (pathSuffixWeight A D p.2.val p.1 y) (homObject A D x p.1.val)))
  exact cochainAcyclic_of_iso hc (fixedLengthSuffixIso A D S x y n).symm

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonGradedTensor

/-! ## DerivedComparisonGradedModule（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonGradedModule.lean） -/

/-! # 固定長 path の直和を右 dg 加群として表す -/

@[expose] public section DerivedComparisonGradedModule
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [DGCategory A D] in
lemma selectedComplexColimits (S : Set D) (P : Word S → Prop) :
    HasColimitsOfShape (Discrete {w : Word S // P w}) (Complex A) := by
  have : HasColimitsOfShape (Discrete {w : Word S // P w}) (ModuleCat.{u} A) :=
    hasColimitsOfShape_of_equivalence
      (Discrete.equivalence (equivShrink.{u} {w : Word S // P w}).symm)
  exact ⟨fun F => HasColimit.mk
    ⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩

/-- 指定された word 部分集合の path 加群の直和。 -/
abbrev selectedPathModule (S : Set D) (P : Word S → Prop) (z : D) : ModuleCategory A D :=
  ∐ (fun w : {w : Word S // P w} => ForgetEnrichment.of (Complex A) (pathModule A D w.val z))

def selectedPathModuleEvaluationIso (S : Set D) (P : Word S → Prop) (z : D) (x : Dᵒᵖ) :
    (moduleEvaluation A D x.unop).obj (selectedPathModule A D S P z) ≅
      selectedHom A D S P x.unop z := by
  have := selectedComplexColimits A D S P
  exact PreservesCoproduct.iso (moduleEvaluation A D x.unop)
      (fun w : {w : Word S // P w} => ForgetEnrichment.of (Complex A) (pathModule A D w.val z)) ≪≫
    Sigma.mapIso
      (f := fun w : {w : Word S // P w} => (moduleEvaluation A D x.unop).obj
        (ForgetEnrichment.of (Complex A) (pathModule A D w.val z)))
      (g := fun w : {w : Word S // P w} => term A D w.val x.unop z)
      (fun w => pathModuleValueIso A D w.val z x)

@[reassoc] lemma selectedPathModuleEvaluationIso_ι (S : Set D) (P : Word S → Prop)
    (z : D) (x : Dᵒᵖ) (w : {w : Word S // P w}) :
    (moduleEvaluation A D x.unop).map (Sigma.ι
      (fun w : {w : Word S // P w} => ForgetEnrichment.of (Complex A) (pathModule A D w.val z)) w) ≫
        (selectedPathModuleEvaluationIso A D S P z x).hom =
      (pathModuleValueIso A D w.val z x).hom ≫
        Sigma.ι (fun w : {w : Word S // P w} => term A D w.val x.unop z) w := by
  have := selectedComplexColimits A D S P
  let hcol := isColimitOfHasCoproductOfPreservesColimit (moduleEvaluation A D x.unop)
    (fun w : {w : Word S // P w} => ForgetEnrichment.of (Complex A) (pathModule A D w.val z))
  have h := hcol.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨w⟩
  change (moduleEvaluation A D x.unop).map (Sigma.ι
      (fun w : {w : Word S // P w} => ForgetEnrichment.of (Complex A) (pathModule A D w.val z)) w) ≫
    (PreservesCoproduct.iso (moduleEvaluation A D x.unop)
      (fun w : {w : Word S // P w} =>
        ForgetEnrichment.of (Complex A) (pathModule A D w.val z))).hom =
    Sigma.ι (fun w : {w : Word S // P w} => (moduleEvaluation A D x.unop).obj
      (ForgetEnrichment.of (Complex A) (pathModule A D w.val z))) w at h
  dsimp only [selectedPathModuleEvaluationIso, Iso.trans_hom]
  rw [← Category.assoc, h, Sigma.ι_mapIso_hom]

/-- 評価同型は、内部先頭作用と全次数で可換である。 -/
lemma selectedPathModuleEvaluationIso_action (S : Set D) (P : Word S → Prop) (z : D)
    (x y : Dᵒᵖ) :
    moduleActionChain A (ForgetEnrichment.to (Complex A) (selectedPathModule A D S P z)) x y ≫
        (selectedPathModuleEvaluationIso A D S P z y).hom =
      ((x ⟶[Complex A] y) ◁ (selectedPathModuleEvaluationIso A D S P z x).hom) ≫
        selectedPrepend A D S P y.unop x.unop z := by
  let F := fun w : {w : Word S // P w} =>
    ForgetEnrichment.of (Complex A) (pathModule A D w.val z)
  let hcol := isColimitOfHasCoproductOfPreservesColimit (moduleEvaluation A D x.unop) F
  apply (isColimitOfPreserves (tensorLeft (x ⟶[Complex A] y)) hcol).hom_ext
  rintro ⟨w⟩
  have hw := moduleMorphism_action_chain A D (Sigma.ι F w) x y
  change moduleActionChain A (pathModule A D w.val z) x y ≫
      (moduleEvaluation A D y.unop).map (Sigma.ι F w) =
    ((x ⟶[Complex A] y) ◁ (moduleEvaluation A D x.unop).map (Sigma.ι F w)) ≫
      moduleActionChain A (ForgetEnrichment.to (Complex A) (selectedPathModule A D S P z)) x y at hw
  change ((x ⟶[Complex A] y) ◁ (moduleEvaluation A D x.unop).map (Sigma.ι F w)) ≫
      (moduleActionChain A (ForgetEnrichment.to (Complex A) (selectedPathModule A D S P z)) x y ≫
        (selectedPathModuleEvaluationIso A D S P z y).hom) =
    ((x ⟶[Complex A] y) ◁ (moduleEvaluation A D x.unop).map (Sigma.ι F w)) ≫
      (((x ⟶[Complex A] y) ◁ (selectedPathModuleEvaluationIso A D S P z x).hom) ≫
        selectedPrepend A D S P y.unop x.unop z)
  calc
    _ = moduleActionChain A (pathModule A D w.val z) x y ≫
        ((moduleEvaluation A D y.unop).map (Sigma.ι F w) ≫
          (selectedPathModuleEvaluationIso A D S P z y).hom) := by
      rw [← Category.assoc, ← hw, Category.assoc]
    _ = moduleActionChain A (pathModule A D w.val z) x y ≫
        (pathModuleValueIso A D w.val z y).hom ≫
          Sigma.ι (fun w : {w : Word S // P w} => term A D w.val y.unop z) w := by
      rw [selectedPathModuleEvaluationIso_ι]
    _ = ((x ⟶[Complex A] y) ◁ (pathModuleValueIso A D w.val z x).hom) ≫
        prependMap A D w.val y.unop x.unop z ≫
          Sigma.ι (fun w : {w : Word S // P w} => term A D w.val y.unop z) w := by
      rw [← Category.assoc, pathModule_action_value, Category.assoc]
    _ = ((x ⟶[Complex A] y) ◁ (pathModuleValueIso A D w.val z x).hom) ≫
        ((x ⟶[Complex A] y) ◁
          Sigma.ι (fun w : {w : Word S // P w} => term A D w.val x.unop z) w) ≫
            selectedPrepend A D S P y.unop x.unop z := by
      exact congrArg (fun f => ((x ⟶[Complex A] y) ◁
        (pathModuleValueIso A D w.val z x).hom) ≫ f)
          (selectedPrepend_ι A D S P y.unop x.unop z w).symm
    _ = _ := by
      have he := congrArg (fun f => ((x ⟶[Complex A] y) ◁ f) ≫
        selectedPrepend A D S P y.unop x.unop z)
          (selectedPathModuleEvaluationIso_ι A D S P z x w)
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc] at he
      exact he.symm

/-- 正の固定長部分は、S 上の自由右加群の直和。 -/
def fixedLengthModuleFreeIso (S : Set D) (z : D) (n : ℕ) :
    selectedPathModule A D S (fun w => w.length = n + 1) z ≅
      ∐ (fun p : S × LengthWord S n =>
        (freeAt p.1.val).obj (pathSuffixWeight A D p.2.val p.1 z)) :=
  (Sigma.whiskerEquiv (consLengthWordEquiv S n)
    (fun p => pathModuleFreeIso A D p.1 p.2.val z)).symm

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonGradedModule

/-! ## DerivedComparisonLocalHom（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonLocalHom.lean） -/

/-! # 片側 K-flat 条件と S に直交する対象上の Hom 比較

この段階では実際の dg 圏の対象 x,y を扱う。
Verdier 分母を添字とするホモトピー圏内の図式との比較は別工程である。
-/

@[expose] public section DerivedComparisonLocalHom
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

lemma shortExact_quasiIso_f_of_acyclic (S : ShortComplex (Complex A)) (hS : S.ShortExact)
    (h₃ : S.X₃.Acyclic) : QuasiIso S.f := by
  constructor
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hm : Mono (homologyMap S.f i) :=
    (hS.homology_exact₁ (i - 1) i (by change i - 1 + 1 = i; omega)).mono_g_iff.mpr
      ((h₃ (i - 1)).isZero_homology.eq_zero_of_src _)
  have he : Epi (homologyMap S.f i) :=
    (hS.homology_exact₂ i).epi_f_iff.mpr ((h₃ i).isZero_homology.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 空 path の包含を各長さ段階に因子化する。 -/
def originalToLength (S : Set D) (x y : D) (n : ℕ) :
    homObject A D x y ⟶ lengthComplex A D S x y n :=
  lengthZeroMap A D S x y ≫ lengthMap A D S x y (Nat.zero_le n)

@[reassoc] lemma originalToLength_inclusion (S : Set D) (x y : D) (n : ℕ) :
    originalToLength A D S x y n ≫ lengthInclusion A D S x y n =
      originalHomInclusion A D S x y := by
  rw [originalToLength, Category.assoc, lengthMap_inclusion, lengthZeroMap_inclusion]

lemma originalToLength_quasiIso (S : Set D) (x y : D)
    (h : ∀ n, (fixedLengthHom A D S x y (n + 1)).Acyclic) (n : ℕ) :
    QuasiIso (originalToLength A D S x y n) := by
  induction n with
  | zero =>
    rw [originalToLength, lengthMap_refl, Category.comp_id]
    infer_instance
  | succ n ih =>
    have : QuasiIso (lengthMap A D S x y (Nat.le_succ n)) :=
      shortExact_quasiIso_f_of_acyclic A (lengthLayerShortComplex A D S x y n)
        (lengthLayer_shortExact A D S x y n) (h n)
    have hc : originalToLength A D S x y (n + 1) =
        originalToLength A D S x y n ≫ lengthMap A D S x y (Nat.le_succ n) := by
      rw [originalToLength, originalToLength, Category.assoc, lengthMap_comp]
    rw [hc]
    infer_instance

def originalLengthTransformation (S : Set D) (x y : D) :
    (Functor.const ℕ).obj (homObject A D x y) ⟶ lengthDiagram A D S x y where
  app n := originalToLength A D S x y n
  naturality {m n} f := by
    change 𝟙 _ ≫ originalToLength A D S x y n =
      originalToLength A D S x y m ≫ lengthMap A D S x y (leOfHom f)
    rw [Category.id_comp, originalToLength, originalToLength, Category.assoc, lengthMap_comp]

/-- 正の全層が acyclic なら、元の Hom の包含は最終 Hom への擬同型。 -/
lemma originalHomInclusion_quasiIso_of_layers (S : Set D) (x y : D)
    (h : ∀ n, (fixedLengthHom A D S x y (n + 1)).Acyclic) :
    QuasiIso (originalHomInclusion A D S x y) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_of_univLE (ModuleCat.{u} A)
  have : IsConnected ℕ := IsFiltered.isConnected _
  let α := originalLengthTransformation A D S x y
  have : QuasiIso (colimMap α) :=
    complex_colimMap_quasiIso A α (originalToLength_quasiIso A D S x y h)
  let e := (isColimitConstCocone ℕ (homObject A D x y)).coconePointUniqueUpToIso
    (colimit.isColimit ((Functor.const ℕ).obj (homObject A D x y)))
  have he : e.hom = colimit.ι ((Functor.const ℕ).obj (homObject A D x y)) 0 := by
    have h₀ :=
      (isColimitConstCocone ℕ (homObject A D x y)).comp_coconePointUniqueUpToIso_hom
        (colimit.isColimit _) (0 : ℕ)
    change 𝟙 (homObject A D x y) ≫ e.hom =
      colimit.ι ((Functor.const ℕ).obj (homObject A D x y)) 0 at h₀
    simpa only [Category.id_comp] using h₀
  have hc : e.hom ≫ colimMap α ≫ (lengthColimitIso A D S x y).hom =
      originalHomInclusion A D S x y := by
    rw [he, ← Category.assoc, ι_colimMap, Category.assoc, lengthColimitIso_ι]
    exact originalToLength_inclusion A D S x y 0
  rw [← hc]
  infer_instance

/-- Hom(−,S) が K-flat で y が S に右直交するときの、明示的商 Hom との比較。 -/
lemma originalHomInclusion_quasiIso_into (S : Set D) (h : homIntoKFlat A D S) (x y : D)
    (hy : ∀ b : S, (homObject A D b.val y).Acyclic) :
    QuasiIso (originalHomInclusion A D S x y) :=
  originalHomInclusion_quasiIso_of_layers A D S x y
    (fixedLengthHom_acyclic_into A D S h x y hy)

/-- Hom(S,−) が K-flat で x が S に左直交するときの、明示的商 Hom との比較。 -/
lemma originalHomInclusion_quasiIso_outOf (S : Set D) (h : homOutOfKFlat A D S) (x y : D)
    (hx : ∀ b : S, (homObject A D x b.val).Acyclic) :
    QuasiIso (originalHomInclusion A D S x y) :=
  originalHomInclusion_quasiIso_of_layers A D S x y
    (fixedLengthHom_acyclic_outOf A D S h x y hx)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonLocalHom
