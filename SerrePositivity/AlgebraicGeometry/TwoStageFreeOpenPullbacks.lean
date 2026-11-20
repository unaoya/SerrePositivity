module

public import SerrePositivity.AlgebraicGeometry.BoundaryFreeOpenLocality
public import SerrePositivity.AlgebraicGeometry.BlowupOpenChartCover
public import SerrePositivity.AlgebraicGeometry.ChosenBlowupChartCover
public import SerrePositivity.AlgebraicGeometry.BoundaryFreeNeighborhoodCenterOver

/-!
概要：KST §5、Stacks 0811 の第二段全チャートの自由化を二段 blowup 全体へ接続する。
方針：指定した第一段被覆に付随する第二段被覆を作り、全アフィン引き戻しでの自由化の局所性を使う。
規約：元の代数と加群を保持し、一般階数は第一段チャートごとに異なってよい。
使われ方：二段自由化対象への支配射で元の基底上の一つの blowup に自由化を移す。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory

set_option maxHeartbeats 800000 in
-- 二段の従属チャート被覆と係数環の同一視を照合するため。
set_option backward.isDefEq.respectTransparency false in
/--
概要：指定した第一段被覆の各制限中心の全チャートで自由化できれば、二段 blowup は全 Noether アフィン引き戻しで自由化基本開を持つ。
方針：第二段の実際のチャート被覆の構造射を元の係数写像と照合し、開被覆に関する局所性を適用する。
規約：KST §5、Stacks 0811、Noether 基底と元の代数の実分裂を仮定する。
使われ方：全第二段チャートで構成した自由化を支配射で保存できる大域の性質へまとめる。
-/
theorem hasBoundaryFreeOpenPullbacks_twoStage
    {A : CommRingCat.{u}} (B : Type u) [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M ι : Type*} [AddCommGroup M] [Module B M] [Module.Finite B M]
    (e : B →ₗ[A] (ι →₀ A)) (s : (ι →₀ A) →ₗ[A] B) (hse : s.comp e = LinearMap.id)
    (I : Ideal A) {κ : Type v} (a : κ → I)
    (hcover : (⨆ i, affineBlowupChart I (a i)) = ⊤)
    (L : (affineBlowup I).IdealSheafData) (f : A)
    (hfree : ∀ i,
      let C := BlowupChartRing I (a i)
      letI : Algebra A C := (chartBaseMap I (a i)).toAlgebra
      BoundaryFreeNeighborhoodsAtCenterOver A B C M (chartBaseMap I (a i) f)
        (specIdealEquiv (.of C) (L.comap (affineBlowupChartι I (a i))))) :
    HasBoundaryFreeOpenPullbacks B (blowupπ L ≫ affineBlowupπ I) f M := by
  let 𝒰 := affineBlowupChosenChartCover I a hcover
  let 𝒱 := blowupOpenChartCover L 𝒰
  apply hasBoundaryFreeOpenPullbacks_of_openCover B e s hse
    (blowupπ L ≫ affineBlowupπ I) f 𝒱.openCover
  intro t
  let i : κ := t.1
  let C := BlowupChartRing I (a i)
  let : Algebra A C := (chartBaseMap I (a i)).toAlgebra
  let J := specIdealEquiv (.of C) (L.comap (affineBlowupChartι I (a i)))
  let b : J := t.2
  let E := BlowupChartRing J b
  let : Algebra A E := ((chartBaseMap J b).comp (chartBaseMap I (a i))).toAlgebra
  let : IsNoetherianRing C := blowupChartRing_isNoetherianRing I (a i)
  let : IsNoetherianRing E := blowupChartRing_isNoetherianRing J b
  obtain ⟨r, _, _, hN⟩ := hfree i
  have hfreeE : BoundaryPureFreeNeighborhoods A B E M (algebraMap A E f) r := hN b
  have hbase : 𝒱.f t ≫ (blowupπ L ≫ affineBlowupπ I) =
      Spec.map (CommRingCat.ofHom (algebraMap A E)) := by
    have hb := congrArg (fun z => z ≫ affineBlowupπ I) (blowupOpenChartCover_base L 𝒰 t)
    rw [Category.assoc] at hb
    rw [hb, Category.assoc]
    change Spec.map (CommRingCat.ofHom (chartBaseMap J b)) ≫
      (affineBlowupChartι I (a i) ≫ affineBlowupπ I) = _
    have hfirst : affineBlowupChartι I (a i) ≫ affineBlowupπ I =
        Spec.map (CommRingCat.ofHom (chartBaseMap I (a i))) :=
      affineBlowupChartIso_inv_ι_π I (a i)
    rw [hfirst, ← Spec.map_comp]
    rfl
  change HasBoundaryFreeOpenPullbacks B (𝒱.f t ≫ (blowupπ L ≫ affineBlowupπ I)) f M
  rw [hbase]
  exact hasBoundaryFreeOpenPullbacks_spec_of_neighborhoods B E e s hse f r hfreeE

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
