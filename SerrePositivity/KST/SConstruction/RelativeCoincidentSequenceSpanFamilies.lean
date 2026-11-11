module
public import SerrePositivity.KST.SConstruction.RelativeSequenceFamilyRectification
public import SerrePositivity.KST.SConstruction.CoincidentKanSpanFamilies

/-! # 境界で一致する二円柱からの列の相対厳密化
概要：各円柱の定数性を要求せず、境界での一致から全段の相対厳密化を構成する。
方針：境界の共通辺に退化三角形を付け、実適合円柱の境界固定性へ移す。
規約：元の二円柱と全パラメータを保持し、境界三角形の存在を仮定しない。
使われ方：高次入力から得た二脚が変化する族を、元の BF 境界を保つ写像族へ渡す。
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
  (h : ∀ n, (j ▷ (Δ[1] : SSet.{u})) ≫ (a n).h =
    (j ▷ (Δ[1] : SSet.{u})) ≫ (b n).h)

/-- 全段の境界三角形を構成し、元の二円柱の族から実適合円柱を作る。 -/
def relativeSequenceCoincidentSpanHomotopy (n : ℕ) : SSet.Homotopy
    (f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)
    (f n ≫ RawSpectrumMapping.step X Y n) :=
  relativeKanCoincidentSpanComposite j (a n) (b n) (h n)

/-- 構成した全段の適合円柱は、元の指定境界を全時刻で固定する。 -/
lemma relativeSequenceCoincidentSpanHomotopy_boundary (n : ℕ) :
    (j ▷ (Δ[1] : SSet.{u})) ≫ (relativeSequenceCoincidentSpanHomotopy X Y j f d a b h n).h =
      fst T Δ[1] ≫ j ≫ f (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space :=
  relativeKanCoincidentSpanComposite_boundary j (a n) (b n) (h n)

/-- 元の境界で一致する二円柱から、同じ指定族を相対厳密化した実際の列の族。 -/
def relativeSequenceCoincidentSpanRectification : U ⟶ RawSpectrumMapping.space X Y :=
  relativeSequenceFamilyRectification X Y j f
    (relativeSequenceCoincidentSpanHomotopy X Y j f d a b h)
    (relativeSequenceCoincidentSpanHomotopy_boundary X Y j f d a b h)

end SerrePositivity.KST.SConstruction
