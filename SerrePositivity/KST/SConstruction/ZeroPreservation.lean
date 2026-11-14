module
public import SerrePositivity.KST.SConstruction.SConstructionStability
public import SerrePositivity.KST.SConstruction.Postcomposition

/-! # S 構成の構造射の零対象の保存
概要：零図式の式から全ての零対象に対する保存を得る。
方針：任意の零対象を定値零図式と同型で比較する。
規約：特定の chosen zero の厳密な保存は要求しない。使われ方：反復の構造射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：一つの零対象の像が零なら全ての零対象の像が零。
方針：零対象間の同型を射で写す。
規約：quasicategory 間の任意の射。使われ方：零図式からの保存判定。 -/
lemma map_isZeroVertex_of_zero_image {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (f : C ⟶ D) (z : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z)
    (hfz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (f.app (Opposite.op ⦋0⦌) z))
    {w : C _⦋0⦌} (hw : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex w) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (f.app (Opposite.op ⦋0⦌) w) :=
  hfz.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.zeroVertexIso ⟨z, hz.1, hz.2⟩ ⟨w, hw.1, hw.2⟩) f)

/-- 概要：gapped 図式の包含は零対象を保存する。
方針：定値零図式を含めた像が零であることを使う。
規約：C は零対象を持つ quasicategory。使われ方：Ar の各点での零対象評価。 -/
lemma gappedInclusion_isZeroVertex {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C]
    (n : ℕ) {v : (sConstruction n C) _⦋0⦌} (hv : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex v) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((gappedSubcomplex n C).ι.app (Opposite.op ⦋0⦌) v) := by
  let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C
  apply map_isZeroVertex_of_zero_image (C := sConstruction n C)
    (D := (ihom (arNerve n)).obj C) (gappedSubcomplex n C).ι
    (sConstructionZeroVertex n z.vertex z.isZero) (sConstructionZeroVertex_isZero n _ _) _ hv
  exact functor_const_isZeroVertex z.vertex z.isZero

/-- 概要：S_n の全ての面・退化写像は零対象を保存する。
方針：零図式の厳密な保存と零対象の同型不変性を使う。
規約：C の安定性は不要。使われ方：多単体的反復の構造射。 -/
lemma sMap_isZeroVertex {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C]
    {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1))
    {v : (sConstruction n C) _⦋0⦌} (hv : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex v) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((sMap C θ).app (Opposite.op ⦋0⦌) v) := by
  let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C
  apply map_isZeroVertex_of_zero_image (sMap C θ) (sConstructionZeroVertex n z.vertex z.isZero)
    (sConstructionZeroVertex_isZero n _ _) _ hv
  rw [sMap_zeroVertex]
  exact sConstructionZeroVertex_isZero m _ _

/-- 概要：保存条件を満たす射の S_n への作用は零対象を保存する。
方針：零図式の後合成の式と像の零頂点を使う。
規約：chosen zero の一致は不要。使われ方：K の関手性の反復。 -/
lemma sPostcomp_isZeroVertex {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] (n : ℕ) (f : C ⟶ D) (hf : PreservesSConstructionData f)
    {v : (sConstruction n C) _⦋0⦌} (hv : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex v) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((sPostcomp n f hf).app (Opposite.op ⦋0⦌) v) := by
  let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C
  apply map_isZeroVertex_of_zero_image (sPostcomp n f hf)
    (sConstructionZeroVertex n z.vertex z.isZero) (sConstructionZeroVertex_isZero n _ _) _ hv
  rw [sPostcomp_zeroVertex]
  exact sConstructionZeroVertex_isZero n _ _

end SerrePositivity.KST.SConstruction
