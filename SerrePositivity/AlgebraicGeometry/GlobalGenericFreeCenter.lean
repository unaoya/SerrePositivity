module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.TwoStageGenericFreeCenters
public import SerrePositivity.AlgebraicGeometry.DisjointBlowupChartCenter

/-!
概要：KST §5、Stacks 0811 の階数一定化後の自由化中心の大域化。
方針：各有限開閉チャートの実際の中心を選び、正確な制限等式を持つ一つのイデアル層に貼り合わせる。
規約：実分裂の下での二段構成を扱い、一般の平坦化の存在は仮定しない。
使われ方：第一段の blowup 上に実際の第二段の大域中心を用意する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：固定した中心の全チャートで基礎環を覆う共通階数の自由化基本開が存在する条件。
方針：有限生成性、中心補開集合、共通自由階数、自由化元の存在を一つの結論にまとめる。
規約：KST §5、Stacks 0810・0811、実際の中心を引数とする述語。
使われ方：中心の制限イデアルの等式に沿って自由化基本開の存在を運ぶ。
-/
def BoundaryFreeNeighborhoodsAtCenter (A B : Type u) (M : Type*)
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module B M]
    (f : A) (J : Ideal A) : Prop :=
  ∃ s : ℕ, J.FG ∧ affineCenterComplement J = PrimeSpectrum.basicOpen f ∧
    ∀ b : J,
      let C := BlowupChartRing J b
      letI : Algebra A C := (chartBaseMap J b).toAlgebra
      BoundaryPureFreeNeighborhoods A B C M (chartBaseMap J b f) s

/--
概要：境界外で相対平坦な有限加群に、第一段の blowup 上の一つの大域自由化中心が存在する。
方針：階数を分離する中心を選び、各開閉チャートで選んだ自由化中心を正確な制限等式付きで貼り合わせる。
規約：KST §5、Stacks 0811, Lemma 38.30.3 の Noether・実分裂の二段構成。
使われ方：二段目の中心を局所的な存在だけでなく一つの実際のイデアル層として保持する。
-/
theorem exists_global_twoStage_boundaryFreeNeighborhood_center
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M ι : Type*} [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M]
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (f : A) (hf : IsRegular f)
    [Module.Flat (Localization.Away f) ((Localization.Away f) ⊗[A] M)] :
    ∃ (I : Ideal A) (a : Set.range (boundaryGenericRank A B M f) → I),
      I.FG ∧ affineCenterComplement I = PrimeSpectrum.basicOpen f ∧
      (⨆ i, affineBlowupChart I (a i)) = ⊤ ∧
      Pairwise (fun i k => Disjoint (affineBlowupChart I (a i)) (affineBlowupChart I (a k))) ∧
      ∃ L : (affineBlowup I).IdealSheafData,
        (∀ V : (affineBlowup I).affineOpens, (L.ideal V).FG) ∧
        centerComplement L = affineBlowupπ I ⁻¹ᵁ PrimeSpectrum.basicOpen f ∧
        ∀ i,
          let C := BlowupChartRing I (a i)
          letI : Algebra A C := (chartBaseMap I (a i)).toAlgebra
          let D := C ⊗[A] B
          letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
          BoundaryFreeNeighborhoodsAtCenter C D (D ⊗[B] M) (chartBaseMap I (a i) f)
            (specIdealEquiv (.of C) (L.comap (affineBlowupChartι I (a i)))) := by
  classical
  let : Fintype (Set.range (boundaryGenericRank A B M f)) :=
    (isLocallyConstant_boundaryGenericRank A B M e p hpe f).range_finite.fintype
  obtain ⟨I, a, hfg, hI, hcover, hdisj, hsecond⟩ :=
    exists_twoStage_boundaryFreeNeighborhood_centers A B (M := M) e p hpe f hf
  let J (i : Set.range (boundaryGenericRank A B M f)) : Ideal (BlowupChartRing I (a i)) :=
    Classical.choose (hsecond i)
  have hJ (i : Set.range (boundaryGenericRank A B M f)) :
      affineCenterComplement (J i) = PrimeSpectrum.basicOpen (chartBaseMap I (a i) f) := by
    exact (Classical.choose_spec (Classical.choose_spec (hsecond i))).2.1
  obtain ⟨L, hLfg, hLU, hrest⟩ := exists_disjointBlowupChart_center I a hcover hdisj f J hJ
  refine ⟨I, a, hfg, hI, hcover, hdisj, L, hLfg, hLU, ?_⟩
  intro i
  dsimp only
  rw [hrest i]
  exact Classical.choose_spec (hsecond i)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
