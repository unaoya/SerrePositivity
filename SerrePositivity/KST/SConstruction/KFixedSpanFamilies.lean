module
public import SerrePositivity.KST.SConstruction.KRelativeFamilyRectification
public import SerrePositivity.KST.SConstruction.RelativeFixedSequenceSpanFamilies

/-! # 元の定数境界の二円柱から BF K の相対写像族へ
概要：全段の二円柱が境界を固定すれば、境界三角形を追加せず BF K の相対族を作る。
方針：元の定数性から退化境界三角形と恒等合成辺を構成し、相対厳密化へ渡す。
規約：全パラメータの二円柱と元の BF 境界の射影の式は実データとして要求する。
使われ方：元の prism の二切断円柱から、指定 BF 境界を保つ実写像族への接続。
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
  (ha : ∀ n, (j ▷ (Δ[1] : SSet.{u})) ≫ (a n).h = fst T Δ[1] ≫ j ≫ d n)
  (hb : ∀ n, (j ▷ (Δ[1] : SSet.{u})) ≫ (b n).h = fst T Δ[1] ≫ j ≫ d n)
  (c : T ⟶ OmegaSpectrum.mappingSpace (kOmegaSpectrum X) (kOmegaSpectrum Y))
  (hc : ∀ n, c ≫ OmegaSpectrum.evaluation (kOmegaSpectrum X) (kOmegaSpectrum Y) n ≫
    (PointedObject.basedHomMap ((kOmegaSpectrum X).level n).space
      ((monicKKanSequenceProjection Y).app n)).right = j ≫ f n)

/-- 元の固定境界の二円柱から、境界の全三角形を構成して実 BF K 写像族を作る。 -/
def relativeKFixedSpanFamilyRectificationData :
    {l : U ⟶ OmegaSpectrum.mappingSpace (kOmegaSpectrum X) (kOmegaSpectrum Y) //
      j ≫ l = c ∧ l ≫ kRawMappingProjection X Y =
        relativeSequenceFixedSpanRectification (kOmegaSpectrum X) (kKanSequence Y)
          j f d a b ha hb} :=
  relativeKFamilyRectificationData X Y j f
    (relativeSequenceFixedSpanHomotopy (kOmegaSpectrum X) (kKanSequence Y) j f d a b ha hb)
    (relativeSequenceFixedSpanHomotopy_boundary (kOmegaSpectrum X) (kKanSequence Y)
      j f d a b ha hb) c hc

/-- 構成した族は、元の指定 BF 境界そのものに厳密に制限される。 -/
lemma relativeKFixedSpanFamilyRectificationData_boundary :
    j ≫ (relativeKFixedSpanFamilyRectificationData X Y j f d a b ha hb c hc).val = c :=
  (relativeKFixedSpanFamilyRectificationData X Y j f d a b ha hb c hc).property.1

/-- 元の未置換列への射影は、退化境界三角形を保持した同じ相対厳密化。 -/
lemma relativeKFixedSpanFamilyRectificationData_projection :
    (relativeKFixedSpanFamilyRectificationData X Y j f d a b ha hb c hc).val ≫
      kRawMappingProjection X Y =
        relativeSequenceFixedSpanRectification (kOmegaSpectrum X) (kKanSequence Y)
          j f d a b ha hb :=
  (relativeKFixedSpanFamilyRectificationData X Y j f d a b ha hb c hc).property.2

end SerrePositivity.KST.SConstruction
