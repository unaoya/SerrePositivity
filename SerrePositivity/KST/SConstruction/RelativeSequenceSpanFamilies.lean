module
public import SerrePositivity.KST.SConstruction.RelativeKanSpanFamilies
public import SerrePositivity.KST.SConstruction.RelativeSequenceFamilyRectification

/-! # 指定した二つの辺の族から列の相対厳密化へ
概要：各段の二つの適合円柱の族と境界の逆・合成三角形から、全段の厳密な写像族を作る。
方針：関手空間で境界の合成を保って相対合成し、境界の恒等辺から定数性を導く。
規約：辺の族と境界三角形は実データとして要求する。元の prism の高次復号は別工程。
使われ方：prism から復号する全パラメータの span と、BF 列の相対厳密化との接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) {T U : SSet.{u}}
  (j : T ⟶ U) [Mono j]
  (f : ∀ n, U ⟶ (PointedObject.basedHom (X.level n).space (Y.level n).space).right)
  (d : ∀ n, U ⟶ (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
    (Y.level (n + 1)).space).right)
  (a : ∀ n, SSet.Homotopy (d n)
    (f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space))
  (b : ∀ n, SSet.Homotopy (d n) (f n ≫ RawSpectrumMapping.step X Y n))
  (t : ∀ n, KanSpanTriangleData
    ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (a n))).map ((pre j).app _))
    ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (b n))).map ((pre j).app _)))

/-- 境界の指定逆・合成三角形を保つ、列の全段の実適合ホモトピー。 -/
def relativeSequenceSpanHomotopy (n : ℕ) : SSet.Homotopy
    (f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)
    (f n ≫ RawSpectrumMapping.step X Y n) :=
  relativeKanHomotopySpanComposite j (a n) (b n) (t n)

variable (ht : ∀ n, (t n).edge.edge = (SSet.Truncated.Edge.id
    (X := (truncation 2).obj ((ihom T).obj
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 1)).space).right))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ f (n + 1) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space))).edge)

include ht

/-- 境界の指定合成辺の恒等性から、全段の厳密化に必要な境界定数性を回収する。 -/
lemma relativeSequenceSpanHomotopy_boundary (n : ℕ) :
    (j ▷ (Δ[1] : SSet.{u})) ≫ (relativeSequenceSpanHomotopy X Y j f d a b t n).h =
      fst T (Δ[1] : SSet.{u}) ≫ j ≫ f (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space :=
  relativeKanHomotopySpanComposite_restrict_constant j (a n) (b n) (t n) (ht n)

/-- 全段の二つの元の円柱の族と境界の指定三角形から作る、境界固定の厳密な列の族。 -/
def relativeSequenceSpanRectification : U ⟶ RawSpectrumMapping.space X Y :=
  relativeSequenceFamilyRectification X Y j f (relativeSequenceSpanHomotopy X Y j f d a b t)
    (relativeSequenceSpanHomotopy_boundary X Y j f d a b t ht)

/-- 構成した列の族は、全段で元の指定した境界を厳密に回収する。 -/
lemma relativeSequenceSpanRectification_boundary (n : ℕ) :
    j ≫ relativeSequenceSpanRectification X Y j f d a b t ht ≫
      RawSpectrumMapping.evaluation X Y n = j ≫ f n :=
  relativeSequenceFamilyRectification_boundary X Y j f _ _ n

/-- 全段の補正は元の族と、境界固定の実ホモトピーの有限列で結ばれる。 -/
lemma relativeSequenceSpanRectification_chain (n : ℕ) :
    Nonempty (RelativeFamilyChain j (f n)
      (relativeSequenceSpanRectification X Y j f d a b t ht ≫
        RawSpectrumMapping.evaluation X Y n)) :=
  relativeSequenceFamilyRectification_chain X Y j f _ _ n

/-- 零段は元の族を修正せず厳密に回収する。 -/
lemma relativeSequenceSpanRectification_zero :
    relativeSequenceSpanRectification X Y j f d a b t ht ≫
      RawSpectrumMapping.evaluation X Y 0 = f 0 :=
  relativeSequenceFamilyRectification_zero X Y j f _ _

end SerrePositivity.KST.SConstruction
