module
public import SerrePositivity.KST.SConstruction.RelativeSequenceFamilyRectification
public import SerrePositivity.KST.SConstruction.FixedKanSpanFamilies

/-! # 定数境界の二円柱からの列の全段の相対厳密化
概要：全段で境界固定の二円柱から、境界三角形を内部構成して厳密な列の族を作る。
方針：一般の Ω スペクトルと Kan 列で実適合円柱と境界固定性を先に証明する。
規約：具体的な K 段の展開を使わず、元の指定族と境界の全データを保持する。
使われ方：元の K prism の実二円柱から、元の BF K 境界を保つ写像族への接続。
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
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) {T U : SSet.{u}}
  (j : T ⟶ U) [Mono j]
  (f : ∀ n, U ⟶ (PointedObject.basedHom (X.level n).space (Y.level n).space).right)
  (d : ∀ n, U ⟶ (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
    (Y.level (n + 1)).space).right)
  (a : ∀ n, SSet.Homotopy (d n)
    (f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space))
  (b : ∀ n, SSet.Homotopy (d n) (f n ≫ RawSpectrumMapping.step X Y n))
  (ha : ∀ n, (j ▷ (Δ[1] : SSet.{u})) ≫ (a n).h = fst T Δ[1] ≫ j ≫ d n)
  (hb : ∀ n, (j ▷ (Δ[1] : SSet.{u})) ≫ (b n).h = fst T Δ[1] ≫ j ≫ d n)

/-- 全段の境界三角形を構成し、元の二円柱の族から実適合円柱を作る。 -/
def relativeSequenceFixedSpanHomotopy (n : ℕ) : SSet.Homotopy
    (f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)
    (f n ≫ RawSpectrumMapping.step X Y n) :=
  fixedKanHomotopySpanComposite j (a n) (b n) (ha n) (hb n)

/-- 構成した全段の適合円柱は、元の指定境界を全時刻で固定する。 -/
lemma relativeSequenceFixedSpanHomotopy_boundary (n : ℕ) :
    (j ▷ (Δ[1] : SSet.{u})) ≫ (relativeSequenceFixedSpanHomotopy X Y j f d a b ha hb n).h =
      fst T Δ[1] ≫ j ≫ f (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space :=
  fixedKanHomotopySpanComposite_relative j (a n) (b n) (ha n) (hb n)

/-- 元の固定境界の二円柱から、同じ指定族を相対厳密化した実際の列の族。 -/
def relativeSequenceFixedSpanRectification : U ⟶ RawSpectrumMapping.space X Y :=
  relativeSequenceFamilyRectification X Y j f
    (relativeSequenceFixedSpanHomotopy X Y j f d a b ha hb)
    (relativeSequenceFixedSpanHomotopy_boundary X Y j f d a b ha hb)

end SerrePositivity.KST.SConstruction
