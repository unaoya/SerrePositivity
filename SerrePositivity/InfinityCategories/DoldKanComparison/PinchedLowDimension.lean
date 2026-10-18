module

public import SerrePositivity.InfinityCategories.DoldKanComparison.ResolutionLowDimension

/-!
# pinched Hom の零・一次単体の完全な比較

概要：標準 Hom と coherent pinched Hom の比較は次数零・一で両側の逆を持つ。
方針：低次の解像の射影が同型であることを旗の評価の同値へ移す。
規約：ホモトピー類ではなく実際の単体の型の同値を述べる。
使われ方：HA 1.3.1.17、Kerodon Theorem 4.6.7.5 の写像空間の比較の低次の基底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory DifferentialGraded
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：標準単体からの構成の後に実際の比較を取ると元の標準単体になる。
方針：全次数の片側の逆の等式を型を明示して単体上で評価する。
規約：この回収則だけは低次に限らず全次数に適用できる。
使われ方：HA 1.3.1.17 の低次の両側の逆の一方。 -/
lemma standardCoherentPinchedSimplex_comparison {x y : ClosedCategory R D} {n : ℕ}
    (σ : StandardSimplex R (D := D) x y n) :
    ((coherentPinchedStandardComparison (R := R) (D := D) x y).app
      (Opposite.op ⦋n⦌) (standardCoherentPinchedSimplex σ)).down = σ := by
  exact congrArg (fun f : SSet.uliftFunctor.{v, u}.obj
      (standardHomSpace (R := R) (D := D) x y) ⟶ SSet.uliftFunctor.{v, u}.obj
        (standardHomSpace (R := R) (D := D) x y) ↦
      (f.app (Opposite.op ⦋n⦌) (ULift.up σ)).down)
    (standardHomToCoherentPinched_comp (R := R) (D := D) x y)

/-- 概要：次数が零・一なら標準 Hom から作る pinched 単体の対応は全単射である。
方針：解像の切断を旗の写像へ前合成して標準単体を回収し、射影との両逆則を使う。
規約：任意の可換環と dg 圏で成り立つ。
使われ方：Kerodon Proposition 4.6.7.16 の低次の解像の簡約。 -/
lemma standardCoherentPinchedSimplex_bijective_of_le_one
    {x y : ClosedCategory R D} {n : ℕ} (hn : n ≤ 1) :
    Function.Bijective (fun σ : StandardSimplex R (D := D) x y n ↦
      standardCoherentPinchedSimplex σ) := by
  constructor
  · intro σ τ h
    have he := congrArg (resolutionHomMap (R := R) (D := D)) h
    rw [resolutionHomMap_standard, resolutionHomMap_standard] at he
    have hs := congrArg (fun φ ↦ coherentResolutionSection n ≫ φ) he
    simp only [← Category.assoc, coherentResolutionSection_projection, Category.id_comp] at hs
    exact (SSet.yonedaEquiv (X := standardHomSpace (R := R) (D := D) x y)
      (n := ⦋n⦌)).symm.injective hs
  · intro s
    let φ : (Δ[n] : SSet.{u}) ⟶ standardHomSpace (R := R) (D := D) x y :=
      coherentResolutionSection n ≫ resolutionHomMap s
    refine ⟨SSet.yonedaEquiv φ, ?_⟩
    apply (resolutionHomEquiv x y n).injective
    simp only [resolutionHomEquiv_apply, resolutionHomMap_standard, Equiv.symm_apply_apply]
    change coherentResolutionProjection n ≫
      (coherentResolutionSection n ≫ resolutionHomMap s) = resolutionHomMap s
    rw [← Category.assoc, resolutionProjection_section_of_le_one hn, Category.id_comp]

/-- 概要：低次の実際の標準比較射の後に逆向きの構成を取ると元の pinched 単体になる。
方針：逆向きの構成の全射性で標準単体へ戻し、既存の厳密な片側の逆を適用する。
規約：零・一次単体の等式であり、一般次数のホモトピーとは区別する。
使われ方：HA 1.3.1.17 の比較の反対側の合成の低次の確認。 -/
lemma coherentPinchedStandardComparison_section_of_le_one
    {x y : ClosedCategory R D} {n : ℕ} (hn : n ≤ 1)
    (s : (coherentPinchedHom (R := R) (D := D) x y) _⦋n⦌) :
    standardCoherentPinchedSimplex
      (((coherentPinchedStandardComparison (R := R) (D := D) x y).app
        (Opposite.op ⦋n⦌) s).down) = s := by
  obtain ⟨σ, rfl⟩ := (standardCoherentPinchedSimplex_bijective_of_le_one
    (R := R) (D := D) hn).surjective s
  rw [standardCoherentPinchedSimplex_comparison]

/-- 概要：低次の標準 Hom と coherent pinched Hom は実際の比較射を逆に持つ型の同値。
方針：構成済みの低次の回収則と全次数の片側の逆を合わせる。
規約：順方向は標準単体からの既存の構成、逆方向は標準比較射そのもの。
使われ方：Kerodon Theorem 4.6.7.5 の低次の検査の公開 API。 -/
def standardCoherentPinchedEquivOfLeOne (x y : ClosedCategory R D) {n : ℕ} (hn : n ≤ 1) :
    StandardSimplex R (D := D) x y n ≃
      (coherentPinchedHom (R := R) (D := D) x y) _⦋n⦌ where
  toFun := standardCoherentPinchedSimplex
  invFun s := ((coherentPinchedStandardComparison (R := R) (D := D) x y).app
    (Opposite.op ⦋n⦌) s).down
  left_inv := standardCoherentPinchedSimplex_comparison
  right_inv := coherentPinchedStandardComparison_section_of_le_one hn

end SerrePositivity.InfinityCategories.DoldKanComparison
