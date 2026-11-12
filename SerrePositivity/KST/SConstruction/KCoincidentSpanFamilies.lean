module
public import SerrePositivity.KST.SConstruction.KRelativeFamilyRectification
public import SerrePositivity.KST.SConstruction.RelativeCoincidentSequenceSpanFamilies

/-! # 境界で一致する二円柱から BF K の相対写像族へ
概要：全段の二円柱が境界で互いに一致すれば、元の BF 境界を保つ実写像族を構成する。
方針：一般の列で作った境界固定の相対合成を、元の単射置換の写像空間へ持ち上げる。
規約：個別の円柱の定数性や境界三角形は要求せず、全円柱と元の BF 境界の射影式を保つ。
使われ方：高次 prism の二脚が変化する族を、既存 BF K の実写像族へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
variable (X Y : StableModel.{u}) {T U : SSet.{u}} (j : T ⟶ U) [Mono j]
  (f : ∀ n, U ⟶ (PointedObject.basedHom ((kOmegaSpectrum X).level n).space
    ((kKanSequence Y).level n).space).right)
  (d : ∀ n, U ⟶ (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum X).level n).space)
    ((kKanSequence Y).level (n + 1)).space).right)
  (a : ∀ n, SSet.Homotopy (d n)
    (f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum X).sigma n)
      ((kKanSequence Y).level (n + 1)).space))
  (b : ∀ n, SSet.Homotopy (d n)
    (f n ≫ RawSpectrumMapping.step (kOmegaSpectrum X) (kKanSequence Y) n))
  (h : ∀ n, (j ▷ (Δ[1] : SSet.{u})) ≫ (a n).h =
    (j ▷ (Δ[1] : SSet.{u})) ≫ (b n).h)
  (c : T ⟶ OmegaSpectrum.mappingSpace (kOmegaSpectrum X) (kOmegaSpectrum Y))
  (hc : ∀ n, c ≫ OmegaSpectrum.evaluation (kOmegaSpectrum X) (kOmegaSpectrum Y) n ≫
    (PointedObject.basedHomMap ((kOmegaSpectrum X).level n).space
      ((monicKKanSequenceProjection Y).app n)).right = j ≫ f n)

/-- 元の境界で一致する二円柱から、境界の全三角形を構成して実 BF K 写像族を作る。 -/
def relativeKCoincidentSpanFamilyRectificationData :
    {l : U ⟶ OmegaSpectrum.mappingSpace (kOmegaSpectrum X) (kOmegaSpectrum Y) //
      j ≫ l = c ∧ l ≫ kRawMappingProjection X Y =
        relativeSequenceCoincidentSpanRectification (kOmegaSpectrum X) (kKanSequence Y)
          j f d a b h} :=
  relativeKFamilyRectificationData X Y j f
    (relativeSequenceCoincidentSpanHomotopy (kOmegaSpectrum X) (kKanSequence Y) j f d a b h)
    (relativeSequenceCoincidentSpanHomotopy_boundary (kOmegaSpectrum X) (kKanSequence Y)
      j f d a b h) c hc

/-- 構成した族は、元の指定 BF 境界そのものに厳密に制限される。 -/
lemma relativeKCoincidentSpanFamilyRectificationData_boundary :
    j ≫ (relativeKCoincidentSpanFamilyRectificationData X Y j f d a b h c hc).val = c :=
  (relativeKCoincidentSpanFamilyRectificationData X Y j f d a b h c hc).property.1

/-- 元の未置換列への射影は、退化境界三角形を保持した同じ相対厳密化。 -/
lemma relativeKCoincidentSpanFamilyRectificationData_projection :
    (relativeKCoincidentSpanFamilyRectificationData X Y j f d a b h c hc).val ≫
      kRawMappingProjection X Y =
        relativeSequenceCoincidentSpanRectification (kOmegaSpectrum X) (kKanSequence Y)
          j f d a b h :=
  (relativeKCoincidentSpanFamilyRectificationData X Y j f d a b h c hc).property.2

end SerrePositivity.KST.SConstruction
