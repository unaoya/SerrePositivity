module
public import SerrePositivity.KST.SConstruction.RelativeSequenceSpanFamilies
public import SerrePositivity.KST.SConstruction.KRelativeFamilyRectification

/-! # 指定境界の span の実三角形から BF K の実写像族へ
概要：全段の二円柱の族と境界の逆・合成三角形から、指定 BF 境界を保つ実写像族を作る。
方針：全パラメータの相対合成で適合ホモトピーを構成し、既存の相対厳密化と持ち上げに渡す。
規約：元の prism の高次復号と境界の指定三角形の構成を追加仮定として隠さない。
使われ方：元の K の prism のパラメータ付き復号から BF K の相対界面への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (X Y : StableModel.{u}) {T U : SSet.{u}}
  (j : T ⟶ U) [Mono j]
  (f : ∀ n, U ⟶ (PointedObject.basedHom ((kOmegaSpectrum X).level n).space
    ((kKanSequence Y).level n).space).right)
  (d : ∀ n, U ⟶ (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum X).level n).space)
    ((kKanSequence Y).level (n + 1)).space).right)
  (a : ∀ n, SSet.Homotopy (d n)
    (f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum X).sigma n)
      ((kKanSequence Y).level (n + 1)).space))
  (b : ∀ n, SSet.Homotopy (d n)
    (f n ≫ RawSpectrumMapping.step (kOmegaSpectrum X) (kKanSequence Y) n))
  (t : ∀ n, KanSpanTriangleData
    ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (a n))).map ((pre j).app _))
    ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (b n))).map ((pre j).app _)))

variable (ht : ∀ n, (t n).edge.edge = (SSet.Truncated.Edge.id
    (X := (truncation 2).obj ((ihom T).obj
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum X).level n).space)
        ((kKanSequence Y).level (n + 1)).space).right))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ f (n + 1) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum X).sigma n)
        ((kKanSequence Y).level (n + 1)).space))).edge)

variable
  (c : T ⟶ OmegaSpectrum.mappingSpace (kOmegaSpectrum X) (kOmegaSpectrum Y))
  (hc : ∀ n, c ≫ OmegaSpectrum.evaluation (kOmegaSpectrum X) (kOmegaSpectrum Y) n ≫
    (PointedObject.basedHomMap ((kOmegaSpectrum X).level n).space
      ((monicKKanSequenceProjection Y).app n)).right = j ≫ f n)

/-- 元の全段の span の族と境界の実三角形から、指定 BF 境界を保つ実写像族を作る。 -/
def relativeKSpanFamilyRectificationData :
    {l : U ⟶ OmegaSpectrum.mappingSpace (kOmegaSpectrum X) (kOmegaSpectrum Y) //
      j ≫ l = c ∧ l ≫ kRawMappingProjection X Y =
        relativeSequenceSpanRectification (kOmegaSpectrum X) (kKanSequence Y) j f d a b t ht} :=
  relativeKFamilyRectificationData X Y j f
    (relativeSequenceSpanHomotopy (kOmegaSpectrum X) (kKanSequence Y) j f d a b t)
    (relativeSequenceSpanHomotopy_boundary (kOmegaSpectrum X) (kKanSequence Y) j f d a b t ht) c hc

/-- 全パラメータの構成は元の指定 BF 境界を厳密に回収する。 -/
lemma relativeKSpanFamilyRectificationData_boundary :
    j ≫ (relativeKSpanFamilyRectificationData X Y j f d a b t ht c hc).val = c :=
  (relativeKSpanFamilyRectificationData X Y j f d a b t ht c hc).property.1

/-- BF 族の元の列への射影は、同じ指定 span からの相対厳密化そのもの。 -/
lemma relativeKSpanFamilyRectificationData_projection :
    (relativeKSpanFamilyRectificationData X Y j f d a b t ht c hc).val ≫
      kRawMappingProjection X Y =
        relativeSequenceSpanRectification (kOmegaSpectrum X) (kKanSequence Y) j f d a b t ht :=
  (relativeKSpanFamilyRectificationData X Y j f d a b t ht c hc).property.2

end SerrePositivity.KST.SConstruction
