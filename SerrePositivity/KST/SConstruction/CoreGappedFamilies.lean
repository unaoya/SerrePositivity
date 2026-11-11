module
public import SerrePositivity.KST.SConstruction.EquivalenceDiagramExactness
public import SerrePositivity.KST.SConstruction.DiagramPushoutChoice

/-! # gapped 図式の core への族の持ち上げ
概要：点ごとに gapped で全辺が可逆な族を、S_n の core への実際の射にする。
方針：全部分複体への持ち上げと可逆性の反映を合わせる。
規約：頂点だけの対応ではなく全高次単体を保持する。使われ方：object/core の行の同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：Ar 図式の関手圏は quasicategory。
方針：内部 Hom の quasicategory 性。
規約：C の安定性は不要。使われ方：gapped 包含の可逆性の反映。 -/
instance diagramSpace_quasicategory (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    Quasicategory (diagramSpace n C) :=
  inferInstanceAs (Quasicategory ((ihom (arNerve n)).obj C))

/-- 概要：gapped な頂点だけを持つ族は S_n に持ち上がる。
方針：gapped の全部分複体の普遍条件。
規約：パラメーターは任意。使われ方：core に持ち上げる前の段階。 -/
def gappedFamilyLift {n : ℕ} {K C : SSet.{u}} (F : K ⟶ diagramSpace n C)
    (hF : ∀ k : K _⦋0⦌,
      IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).symm (F.app (Opposite.op ⦋0⦌) k))) :
    K ⟶ sConstruction n C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ F hF

/-- 概要：gapped 族の持ち上げは元の族を保持する。
方針：全部分複体への持ち上げの包含の式。
規約：全単体で厳密な等号。使われ方：交換の逆律。 -/
lemma gappedFamilyLift_ι {n : ℕ} {K C : SSet.{u}} (F : K ⟶ diagramSpace n C)
    (hF : ∀ k : K _⦋0⦌,
      IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).symm (F.app (Opposite.op ⦋0⦌) k))) :
    gappedFamilyLift F hF ≫ (gappedSubcomplex n C).ι = F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ F hF

/-- 概要：全辺が可逆な gapped 族は S_n の core への射に持ち上がる。
方針：gapped 包含の充満忠実性で辺の可逆性を反映する。
規約：標的 C は quasicategory。使われ方：object S の行から core S の行への射。 -/
def coreGappedFamilyLift {n : ℕ} {K C : SSet.{u}} [Quasicategory C]
    (F : K ⟶ diagramSpace n C)
    (hF : ∀ k : K _⦋0⦌,
      IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).symm (F.app (Opposite.op ⦋0⦌) k)))
    (he : ∀ s : K _⦋1⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (F.app (Opposite.op ⦋1⦌) s))) :
    K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C) : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift (gappedFamilyLift F hF) (by
    intro s
    have : Quasicategory (gappedSubcomplex n C : SSet.{u}) :=
      sConstruction_quasicategory n C
    apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _).reflects_isInvertibleEdge
    exact he s)

/-- 概要：core に持ち上げて二つの包含を通すと元の族。
方針：二段の持ち上げの包含の式を使う。
規約：可逆性の証明の選択に依存しない。使われ方：行の比較の厳密な逆律。 -/
lemma coreGappedFamilyLift_ι {n : ℕ} {K C : SSet.{u}} [Quasicategory C]
    (F : K ⟶ diagramSpace n C)
    (hF : ∀ k : K _⦋0⦌,
      IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).symm (F.app (Opposite.op ⦋0⦌) k)))
    (he : ∀ s : K _⦋1⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (F.app (Opposite.op ⦋1⦌) s))) :
    coreGappedFamilyLift F hF he ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C)).ι ≫
      (gappedSubcomplex n C).ι = F := by
  rw [← Category.assoc, coreGappedFamilyLift, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift_ι, gappedFamilyLift_ι]

/-- 概要：内部 Hom の交換後の各頂点が表す図式は、交換前の各点での評価。
方針：交換をもう一度行った後の評価公式と逆律を使う。
規約：添字と標的は任意。使われ方：gapped 条件の交換。 -/
lemma flipFamily_vertex {A B C : SSet.{u}} (F : A ⟶ (ihom B).obj C) (b : B _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A C).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A B C F).app (Opposite.op ⦋0⦌) b) =
      F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b := by
  rw [← flipFamily_evaluate (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A B C F) b]
  exact congrArg (fun q => q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A B C).left_inv F)

end SerrePositivity.KST.SConstruction
