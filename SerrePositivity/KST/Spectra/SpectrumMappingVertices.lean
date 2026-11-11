module

public import SerrePositivity.KST.Spectra.SpectrumMorphisms
public import SerrePositivity.KST.Spectra.TruncatedMappingUniversal

/-!
概要：Ω スペクトルの写像空間の零次単体と厳密な射の比較。
方針：段ごとの評価の整合条件を通常の点つき射の可換条件へ移す。
規約：塔の極限として構成した写像空間を使う。
使われ方：BF 1978 §2、HTT A.3.3。通常の圏と単体的写像空間の接続。
-/

@[expose] public section

universe u

open CategoryTheory SSet MonoidalCategory
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：スペクトルの写像空間から各段の写像空間への評価。
方針：切断写像空間の極限の評価を用いる。
規約：全単体次数での自然な射。
使われ方：BF 1978 §2、HTT A.3.3。スペクトルの射との同定。 -/
abbrev evaluation (X Y : OmegaSpectrum.{u}) (n : ℕ) : mappingSpace X Y ⟶
    (PointedObject.basedHom (X.level n).space (Y.level n).space).right :=
  TruncatedMapping.totalEvaluation _ _ _ X.sigma (mappingStep X Y) n

/-- 概要：各段の評価は構造写像の境界条件を満たす。
方針：切断写像空間の普遍構成の整合条件を特殊化する。
規約：厳密な等式。
使われ方：BF 1978 §2。射の構造可換条件。 -/
@[reassoc]
theorem evaluation_condition (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    evaluation X Y (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
      evaluation X Y n ≫ mappingStep X Y n :=
  TruncatedMapping.totalEvaluation_condition _ _ _ _ _ n

/-- 概要：構造射の境界比較は頂点で suspension と標的構造射との合成になる。
方針：写像空間の suspension と後合成の頂点の計算を使う。
規約：通常の段ごとの点つき射 f。
使われ方：BF 1978 §2、HTT A.3.3。厳密な射の可換条件との照合。 -/
@[simp]
theorem mappingStep_vertex (X Y : OmegaSpectrum.{u}) (n : ℕ)
    (f : (X.level n).space ⟶ (Y.level n).space) :
    (mappingStep X Y n).app _ (pointedHomVertexEquiv _ _ f) =
      pointedHomVertexEquiv _ _ (PointedSimplicialSet.circle.{u} ◁ f ≫ Y.sigma n) := by
  change (PointedObject.basedHomMap _ (Y.sigma n)).right.app _
    ((suspensionHom _ _).right.app _ (pointedHomVertexEquiv _ _ f)) = _
  rw [pointedHomVertexEquiv_suspension, pointedHomVertexEquiv_post]

/-- 概要：写像空間の頂点からスペクトルの厳密な射を作る。
方針：各段の評価を点つき射へ戻し、整合条件を可換条件へ移す。
規約：Ω 条件をこの照合には使わない。
使われ方：BF 1978 §2、HTT A.3.3。写像空間の零次の通常の射への比較。 -/
def homOfVertex {X Y : OmegaSpectrum.{u}} (v : (mappingSpace X Y) _⦋0⦌) : X ⟶ Y where
  app n := (pointedHomVertexEquiv _ _).symm ((evaluation X Y n).app _ v)
  comm n := by
    apply (pointedHomVertexEquiv _ _).injective
    rw [← mappingStep_vertex, ← pointedHomVertexEquiv_pre]
    simp only [Equiv.apply_symm_apply]
    exact (congrArg (fun k : mappingSpace X Y ⟶
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 1)).space).right ↦
        k.app _ v) (evaluation_condition X Y n)).symm

/-- 概要：終対象からの射を頂点として評価する同値は後合成と両立する。
方針：零次の唯一の元で評価する定義を読む。
規約：ここでの終対象は SSet のモノイダル単位。
使われ方：HTT A.3.3。整合する頂点を極限の頂点へまとめる。 -/
theorem unitHomEquiv_comp {B C : SSet.{u}} (f : 𝟙_ SSet.{u} ⟶ B) (g : B ⟶ C) :
    C.unitHomEquiv (f ≫ g) = g.app _ (B.unitHomEquiv f) := rfl

/-- 概要：厳密な射の各段を写像空間の終対象パラメータの射へ移す。
方針：点つき射の頂点表示と終対象からの射の同値を使う。
規約：n 段での実際の点つき射を使う。
使われ方：BF 1978 §2。厳密な射から写像空間の頂点への構成。 -/
def homFamily {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    𝟙_ SSet.{u} ⟶ (PointedObject.basedHom (X.level n).space (Y.level n).space).right :=
  (SSet.unitHomEquiv _).symm (pointedHomVertexEquiv _ _ (f.app n))

/-- 概要：厳密な射の各段を表す終対象からの射は塔の条件を満たす。
方針：構造射との可換条件を頂点表示へ移す。
規約：厳密な等式。
使われ方：BF 1978 §2。極限への普遍的な持ち上げ。 -/
theorem homFamily_condition {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    homFamily f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
      homFamily f n ≫ mappingStep X Y n := by
  apply (SSet.unitHomEquiv _).injective
  rw [unitHomEquiv_comp, unitHomEquiv_comp]
  simp only [homFamily, Equiv.apply_symm_apply, pointedHomVertexEquiv_pre,
    mappingStep_vertex, f.comm]

/-- 概要：厳密なスペクトルの射を終対象パラメータの整合写像へ移す。
方針：段ごとの族を写像空間の普遍性で持ち上げる。
規約：写像空間は既に Kan 性を証明した実際の塔の極限。
使われ方：BF 1978 §2、HTT A.3.3。零次単体の比較。 -/
def vertexOfHomMap {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    𝟙_ SSet.{u} ⟶ mappingSpace X Y :=
  TruncatedMapping.familyLift (fun n ↦ (X.level n).space) (fun n ↦ (Y.level n).space)
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) X.sigma (mappingStep X Y)
    (homFamily f) (homFamily_condition f)

/-- 概要：厳密なスペクトルの射を写像空間の頂点へ移す。
方針：終対象パラメータの整合写像を零次の元で評価する。
規約：各段の点つき射と厳密可換条件を用いる。
使われ方：BF 1978 §2、HTT A.3.3。零次単体の比較。 -/
def vertexOfHom {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) : (mappingSpace X Y) _⦋0⦌ :=
  (mappingSpace X Y).unitHomEquiv (vertexOfHomMap f)

/-- 概要：厳密な射の頂点を各段へ評価すると元の段の射の頂点となる。
方針：整合族の持ち上げの評価計算を頂点に移す。
規約：任意の段 n。
使われ方：BF 1978 §2。両方向の構成の逆関係。 -/
@[simp]
theorem vertexOfHom_evaluation {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    (evaluation X Y n).app _ (vertexOfHom f) = pointedHomVertexEquiv _ _ (f.app n) := by
  have h := TruncatedMapping.familyLift_evaluation
    (fun n ↦ (X.level n).space) (fun n ↦ (Y.level n).space)
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) X.sigma (mappingStep X Y)
    (homFamily f) (homFamily_condition f) n
  have hh := congrArg (SSet.unitHomEquiv _) h
  rw [unitHomEquiv_comp] at hh
  exact hh.trans (Equiv.apply_symm_apply _ _)

/-- 概要：厳密な射を頂点へ移して戻すと元の射となる。
方針：全段の評価で検査する。
規約：構造条件の証明は外延性により一意。
使われ方：BF 1978 §2。通常の射と零次単体の同値。 -/
@[simp]
theorem homOfVertex_vertexOfHom {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    homOfVertex (vertexOfHom f) = f := by
  apply Hom.ext
  intro n
  change (pointedHomVertexEquiv _ _).symm ((evaluation X Y n).app _ (vertexOfHom f)) = _
  rw [vertexOfHom_evaluation, Equiv.symm_apply_apply]

/-- 概要：写像空間の頂点は各段への評価で決まる。
方針：終対象からの射に戻して全切断の普遍性を使う。
規約：全ての自然数段で評価する。
使われ方：BF 1978 §2、HTT A.3.3。頂点の比較の一意性。 -/
theorem vertex_ext {X Y : OmegaSpectrum.{u}} {v w : (mappingSpace X Y) _⦋0⦌}
    (h : ∀ n, (evaluation X Y n).app _ v = (evaluation X Y n).app _ w) : v = w := by
  apply (SSet.unitHomEquiv (mappingSpace X Y)).symm.injective
  apply TruncatedMapping.total_hom_ext (fun n ↦ (X.level n).space)
    (fun n ↦ (Y.level n).space) (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
    X.sigma (mappingStep X Y)
  intro n
  apply (SSet.unitHomEquiv _).injective
  rw [unitHomEquiv_comp, unitHomEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h n

/-- 概要：写像空間の頂点を厳密な射へ移して戻すと元の頂点となる。
方針：全段の評価を点つき射の頂点表示と比較する。
規約：切断の極限の実際の一意性を使う。
使われ方：BF 1978 §2、HTT A.3.3。通常の射と零次単体の同値。 -/
@[simp]
theorem vertexOfHom_homOfVertex {X Y : OmegaSpectrum.{u}} (v : (mappingSpace X Y) _⦋0⦌) :
    vertexOfHom (homOfVertex v) = v := by
  apply vertex_ext
  intro n
  rw [vertexOfHom_evaluation]
  exact Equiv.apply_symm_apply _ _

/-- 概要：厳密なスペクトルの射と写像空間の零次単体の同値。
方針：各段評価と整合族への普遍的な持ち上げを互いに逆と示す。
規約：定義した Hom の可換条件と単体集合の整合条件を同定する。
使われ方：BF 1978 §2、HTT A.3.3。単体的圏の通常の圏との接続。 -/
def homVertexEquiv (X Y : OmegaSpectrum.{u}) : (X ⟶ Y) ≃ (mappingSpace X Y) _⦋0⦌ where
  toFun := vertexOfHom
  invFun := homOfVertex
  left_inv := homOfVertex_vertexOfHom
  right_inv := vertexOfHom_homOfVertex

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
