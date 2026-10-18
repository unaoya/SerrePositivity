module

public import SerrePositivity.KST.DerivedGeometry.CochainDisk
public import SerrePositivity.KST.DerivedGeometry.ContractibleInjectiveEnvelope
public import SerrePositivity.KST.DerivedGeometry.GeneratorInjectiveFactorCriterion

/-!
概要：二項複体の injective 埋め込みに対する持ち上げから各項 injectivity を得る。
方針：評価の corepresentability で部分対象からの射を鎖写像にし、injective 因子化を作る。
規約：実際の生成対象の全部分対象を試験する。
使われ方：Stacks 19.12.5・19.12.6、TT §3・§8、Toën §3.2 の非有界分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v u
open CategoryTheory Limits ZeroObject
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/--
概要：二項複体の持ち上げは指定した項への射の injective 因子化を与える。
方針：評価の corepresentability と持ち上げの成分等式を使う。
規約：因子の中間対象は既に構成された injective envelope の項。
使われ方：Stacks 19.12.5・19.12.6、TT §3 の各項 injectivity。
-/
lemma diskEnvelope_injective_factor (I : CochainComplex C ℤ) (X : C) (n : ℤ)
    [HasLiftingProperty (termInjectiveEnvelopeι (cochainDisk X n)) (0 : I ⟶ 0)]
    (f : X ⟶ I.X n) :
    ∃ (J : C) (_ : Injective J) (a : X ⟶ J) (b : J ⟶ I.X n), a ≫ b = f := by
  let H := HomologicalComplex.evalCompCoyonedaCorepresentableByDoubleId
    (hi₀₁ := show (ComplexShape.up ℤ).Rel n (n + 1) from rfl) (by omega) X
  let u : cochainDisk X n ⟶ I := H.homEquiv.symm f
  let sq : CommSq u (termInjectiveEnvelopeι (cochainDisk X n)) (0 : I ⟶ 0)
      (0 : termInjectiveEnvelope (cochainDisk X n) ⟶ 0) := ⟨by simp⟩
  refine ⟨_, inferInstance,
    (HomologicalComplex.doubleXIso₀ _ _).inv ≫
      (termInjectiveEnvelopeι (cochainDisk X n)).f n, sq.lift.f n, ?_⟩
  rw [Category.assoc, ← HomologicalComplex.comp_f, sq.fac_left]
  exact H.homEquiv.apply_symm_apply f

/--
概要：生成対象の部分対象の二項複体を全て持ち上げる複体の各項は injective。
方針：生成対象による injective 判定へ上の具体的因子化を渡す。
規約：全 K-injective 性とは区別する。
使われ方：Stacks 19.12.6、TT §3・§8、Toën §3.2 の非有界分解の各項。
-/
lemma injective_components_of_disk_envelope_lifting (G : C) (hG : IsSeparator G)
    (I : CochainComplex C ℤ)
    (h : ∀ (S : Subobject G) (n : ℤ),
      HasLiftingProperty (termInjectiveEnvelopeι (cochainDisk (S : C) n)) (0 : I ⟶ 0))
    (n : ℤ) : Injective (I.X n) := by
  apply injective_of_generator_injective_factors G hG (I.X n)
  intro S f
  have := h S n
  exact diskEnvelope_injective_factor I (S : C) n f

end SerrePositivity.KST.DerivedGeometry
