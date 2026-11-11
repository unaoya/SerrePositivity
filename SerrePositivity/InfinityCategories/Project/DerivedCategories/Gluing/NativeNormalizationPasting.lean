module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeNormalizationTriangleFamilies

/-! # 共有面に沿う実正規化 cube の貼り合わせ

概要：前後の実正規化 cube を、同じ共有面を持つ一つの射へ貼り合わせる。
方針：共有面の二つの包含の pushout を取り、両 cube の射から実射を作る。
規約：全 cube を保持するため、元面・係数面と側面の合成三角形を同時に保持する。
使われ方：固定辺が変わる側面も含め、指定対角境界へ相対比較を移す。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial

/-- 概要：前 cube の内側零面を選ぶ。
方針：二つの外側区間を保持する。規約：元 Hom 入力を変えない。
使われ方：前後 cube の共通面の第一包含。 -/
def dgGluingNormalizationPastingLeftFace (P : SSet.{u}) :=
  (Δ[1] : SSet.{u}) ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 P)

/-- 概要：後 cube の中間零面を選ぶ。
方針：外側区間と内側の区間族を保持する。規約：元 Hom 入力を変えない。
使われ方：前後 cube の共通面の第二包含。 -/
def dgGluingNormalizationPastingRightFace (P : SSet.{u}) :=
  (Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ P)

/-- 概要：二つの正規化 cube を共有面で貼った実単体集合。
方針：同じ二次元面からの二包含の pushout を取る。
規約：側面は潰さない。使われ方：augmentation と標準合成三角形の同時比較。 -/
abbrev dgGluingNormalizationPastingDomain (P : SSet.{u}) :=
  pushout (dgGluingNormalizationPastingLeftFace P) (dgGluingNormalizationPastingRightFace P)

variable {P Z : SSet.{u}}
  (V W : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ (Δ[1] ⊗ P)) ⟶ Z)
  (h : dgGluingNormalizationPastingLeftFace P ≫ V =
    dgGluingNormalizationPastingRightFace P ≫ W)

/-- 概要：共通面で一致する二 cube を一つの実射へ貼り合わせる。
方針：pushout の普遍性を使う。規約：存在だけでなく二つの元射を回収する。
使われ方：native 前後 cube と全側面の正本となる貼り合わせ射。 -/
def dgGluingNormalizationPasting : dgGluingNormalizationPastingDomain P ⟶ Z :=
  pushout.desc V W h

lemma dgGluingNormalizationPasting_left :
    pushout.inl _ _ ≫ dgGluingNormalizationPasting V W h = V :=
  pushout.inl_desc _ _ _

lemma dgGluingNormalizationPasting_right :
    pushout.inr _ _ ≫ dgGluingNormalizationPasting V W h = W :=
  pushout.inr_desc _ _ _

variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "P₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePinchedHomParameter R C D M X Y

/-- 概要：実導来加群上の前後 cube を、その共有面で貼り合わせる。
方針：既に証明済みの全二次元族の一致を使う。
規約：元 C・D・M の宇宙を制限しない。使われ方：③の側面を含む相対比較。 -/
def dgGluingNativeNormalizationPasting :=
  dgGluingNormalizationPasting
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPreNormalizeCube R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPostNormalizeCube R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedNormalizationCube_shared_face R C D M X Y)

lemma dgGluingNativeNormalizationPasting_left :
    pushout.inl _ _ ≫ dgGluingNativeNormalizationPasting R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPreNormalizeCube R C D M X Y :=
  dgGluingNormalizationPasting_left _ _ _

lemma dgGluingNativeNormalizationPasting_right :
    pushout.inr _ _ ≫ dgGluingNativeNormalizationPasting R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPostNormalizeCube R C D M X Y :=
  dgGluingNormalizationPasting_right _ _ _

lemma dgGluingNativeNormalizationPasting_original :
    ((Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 P₀)) ≫ pushout.inl _ _) ≫
        dgGluingNativeNormalizationPasting R C D M X Y =
      (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomIntervalEvaluation R C D M X Y) ≫
        (β_ (Δ[1] : SSet.{max (u + 1) v w})
          ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)))).hom ≫
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedAugmentationHomotopy R C D M).h := by
  rw [Category.assoc, dgGluingNativeNormalizationPasting_left,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPreNormalizeCube_original_face]

lemma dgGluingNativeNormalizationPasting_canonical :
    ((Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 P₀)) ≫ pushout.inr _ _) ≫
        dgGluingNativeNormalizationPasting R C D M X Y =
      (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismIntervalSquare
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max u v w, max (u + 1) v w} 1
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientAugmentationPrism R C D M X Y))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCanonicalCoefficientIntervalEvaluation R C D M X Y) := by
  rw [Category.assoc, dgGluingNativeNormalizationPasting_right,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPostNormalizeCube_canonical_interval_face]

lemma dgGluingNativeNormalizationPasting_left_side (i : Fin 2) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (Δ[1] ⊗ (Δ[1] ⊗ P₀))) ≫ pushout.inl _ _) ≫
        dgGluingNativeNormalizationPasting R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (Δ[1] ⊗ (Δ[1] ⊗ P₀)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPreNormalizeCube R C D M X Y := by
  rw [Category.assoc, dgGluingNativeNormalizationPasting_left]

lemma dgGluingNativeNormalizationPasting_right_side (i : Fin 2) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (Δ[1] ⊗ (Δ[1] ⊗ P₀))) ≫ pushout.inr _ _) ≫
        dgGluingNativeNormalizationPasting R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (Δ[1] ⊗ (Δ[1] ⊗ P₀)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPostNormalizeCube R C D M X Y := by
  rw [Category.assoc, dgGluingNativeNormalizationPasting_right]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
