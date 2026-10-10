module

public import SerrePositivity.HomologicalAlgebra.TorNaturality

/-! # 両変数の射影分解による Tor の比較

射影的な被覆の核に沿って次数を下げ、一次では零次 Tor の写像の核を比較する。
可換環上の任意の加群について、変数を交換した Tor の線形同値を構成する。
ここで高次の同値の自然性や、交換を二度行うと恒等になることは主張しない。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory Limits MonoidalCategory

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- 完全列の最初の射が単射なら、その始域は次の射の核と線形同値である。 -/
noncomputable def linearEquivKernelOfExact
    {X Y Z : Type u} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module R X] [Module R Y] [Module R Z]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (hf : Function.Injective f) (h : Function.Exact f g) :
    X ≃ₗ[R] LinearMap.ker g :=
  (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.mp h).symm)

/-- 同型による可換正方形は、核の線形同値を誘導する。 -/
noncomputable def linearKerCongr
    {X Y X' Y' : Type u} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']
    [Module R X] [Module R Y] [Module R X'] [Module R Y']
    (f : X →ₗ[R] Y) (g : X' →ₗ[R] Y') (e : X ≃ₗ[R] X') (e' : Y ≃ₗ[R] Y')
    (h : ∀ x, e' (f x) = g (e x)) : LinearMap.ker f ≃ₗ[R] LinearMap.ker g where
  toFun x := ⟨e x, by rw [LinearMap.mem_ker, ← h, x.property, map_zero]⟩
  invFun x := ⟨e.symm x, by
    rw [LinearMap.mem_ker]
    apply e'.injective
    rw [h, e.apply_symm_apply, x.property, map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_add' x y := Subtype.ext (e.map_add x y)
  map_smul' r x := Subtype.ext (e.map_smul r x)

section presentation

variable (K P M N : ModuleCat.{u} R) [Projective P]
  (f : K ⟶ P) (g : P ⟶ M) (hf : Function.Injective f) (hg : Function.Surjective g)
  (he : Function.Exact f g)

/-- 第1変数の射影的な表示から、一次 Tor を零次の標準の射の核として表す。 -/
noncomputable def torOneKernelLeft :
    TorModule R 1 M N ≃ₗ[R]
      LinearMap.ker (((Tor (ModuleCat R) 0).map f).app N).hom := by
  apply Classical.choice
  obtain ⟨α, β, δ, _, hbd, hda, _, ha, _⟩ :=
    torModule_longExact_left_with_maps N f.hom g.hom hf hg he
  have hi : Function.Injective (δ 0) := by
    apply (LinearMap.injective_iff_eq_zero_of_exact (hbd 0)).mpr
    have := torModule_subsingleton_of_flat (R := R) P N 0
    ext x
    rw [Subsingleton.elim x 0, map_zero]
    rfl
  have hd := hda 0
  rw [ha 0] at hd
  exact ⟨linearEquivKernelOfExact (δ 0) _ hi hd⟩

/-- 第2変数の同じ表示から、一次 Tor を零次の標準の射の核として表す。 -/
noncomputable def torOneKernelRight :
    TorModule R 1 N M ≃ₗ[R]
      LinearMap.ker (((Tor (ModuleCat R) 0).obj N).map f).hom := by
  let F := tensorLeft N
  let δ := LeftDerivedLES.δ F f.hom g.hom hf hg he 0
  have hi : Function.Injective δ.hom := by
    apply (LinearMap.injective_iff_eq_zero_of_exact (LeftDerivedLES.exact_βδ F
      f.hom g.hom hf hg he 0)).mpr
    have : Subsingleton ((F.leftDerived 1).obj (ModuleCat.of R P)) :=
      ModuleCat.subsingleton_of_isZero (isZero_Tor_succ_of_projective (ModuleCat R) N P 0)
    ext x
    rw [Subsingleton.elim x 0, map_zero]
    rfl
  have hd := LeftDerivedLES.exact_δα F f.hom g.hom hf hg he 0
  rw [LeftDerivedLES.α_eq_map] at hd
  exact linearEquivKernelOfExact δ.hom _ hi hd

/-- 一次 Tor の変数交換は、零次のテンソル積の交換が与える核の同型から得る。 -/
noncomputable def torOneCommOfPresentation : TorModule R 1 M N ≃ₗ[R] TorModule R 1 N M :=
  (torOneKernelLeft K P M N f g hf hg he).trans
    ((linearKerCongr _ _ (torZeroComm K N).toLinearEquiv (torZeroComm P N).toLinearEquiv
      (fun x ↦ congrArg (fun t ↦ t x) (torZeroComm_naturality_left f N))).trans
      (torOneKernelRight K P M N f g hf hg he).symm)

/-- 第1変数の射影的な被覆の核に沿って、二次以上の Tor の次数を下げる。 -/
noncomputable def torShiftLeft (i : ℕ) :
    TorModule R (i + 2) M N ≃ₗ[R] TorModule R (i + 1) K N := by
  apply Classical.choice
  obtain ⟨α, β, δ, _, hbd, hda, _⟩ := torModule_longExact_left N f.hom g.hom hf hg he
  have hi : Function.Injective (δ (i + 1)) := by
    apply (LinearMap.injective_iff_eq_zero_of_exact (hbd (i + 1))).mpr
    have := torModule_subsingleton_of_flat (R := R) P N (i + 1)
    ext x
    rw [Subsingleton.elim x 0, map_zero]
    rfl
  have hs : Function.Surjective (δ (i + 1)) := by
    apply (LinearMap.surjective_iff_eq_zero_of_exact (hda (i + 1))).mpr
    have := torModule_subsingleton_of_flat (R := R) P N i
    ext x
    exact Subsingleton.elim _ _
  exact ⟨LinearEquiv.ofBijective (δ (i + 1)) ⟨hi, hs⟩⟩

/-- 第2変数の同じ被覆の核に沿って、二次以上の Tor の次数を下げる。 -/
noncomputable def torShiftRight (i : ℕ) :
    TorModule R (i + 2) N M ≃ₗ[R] TorModule R (i + 1) N K := by
  apply Classical.choice
  obtain ⟨α, β, δ, _, hbd, hda, _⟩ := torModule_longExact N f.hom g.hom hf hg he
  have hi : Function.Injective (δ (i + 1)) := by
    apply (LinearMap.injective_iff_eq_zero_of_exact (hbd (i + 1))).mpr
    have := ModuleCat.subsingleton_of_isZero
      (isZero_Tor_succ_of_projective (ModuleCat R) N P (i + 1))
    ext x
    rw [Subsingleton.elim x 0, map_zero]
    rfl
  have hs : Function.Surjective (δ (i + 1)) := by
    apply (LinearMap.surjective_iff_eq_zero_of_exact (hda (i + 1))).mpr
    have := ModuleCat.subsingleton_of_isZero (isZero_Tor_succ_of_projective (ModuleCat R) N P i)
    ext x
    exact Subsingleton.elim _ _
  exact ⟨LinearEquiv.ofBijective (δ (i + 1)) ⟨hi, hs⟩⟩

end presentation

/-- 任意の可換環上の任意の加群について、全次数の Tor は変数交換で線形同値である。
射影被覆の選択による次数の帰納法で構成する。高次の自然性はこの定理には含めない。 -/
noncomputable def torComm (i : ℕ) (M N : ModuleCat.{u} R) :
    TorModule R i M N ≃ₗ[R] TorModule R i N M := by
  cases i with
  | zero => exact (torZeroComm M N).toLinearEquiv
  | succ i =>
    let P := Projective.over M
    let g : P ⟶ M := Projective.π M
    let K := ModuleCat.of R (LinearMap.ker g.hom)
    let f : K ⟶ P := ModuleCat.ofHom (LinearMap.ker g.hom).subtype
    have hf : Function.Injective f := Subtype.val_injective
    have hg : Function.Surjective g := (ModuleCat.epi_iff_surjective g).mp inferInstance
    have he : Function.Exact f g := LinearMap.exact_subtype_ker_map g.hom
    cases i with
    | zero => exact torOneCommOfPresentation K P M N f g hf hg he
    | succ i =>
      exact (torShiftLeft K P M N f g hf hg he i).trans
        ((torComm (i + 1) K N).trans (torShiftRight K P M N f g hf hg he i).symm)
termination_by i

/-- 型として与えた加群に対する Tor の変数交換。 -/
noncomputable def torModuleComm (i : ℕ) (M N : Type u)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    TorModule R i M N ≃ₗ[R] TorModule R i N M :=
  torComm i (ModuleCat.of R M) (ModuleCat.of R N)

/-- 通常の長さは、Tor の変数交換で変わらない。有限長性は不要である。 -/
lemma length_torModule_comm (i : ℕ) (M N : Type u)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    Module.length R (TorModule R i M N) = Module.length R (TorModule R i N M) :=
  (torModuleComm i M N).length_eq

/-- 第1変数の任意の射影コチェイン分解でも、通常の Tor を計算できる。 -/
noncomputable def torModuleIsoCochainLeft (N : Type u) [AddCommGroup N] [Module R N]
    {M : Type u} [AddCommGroup M] [Module R M]
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsResolutionOf K (ModuleCat.of R M)) (i : ℕ) :
    ModuleCat.of R (TorModule R i M N) ≅
      (((tensorLeft (ModuleCat.of R N)).mapHomologicalComplex (.up ℤ)).obj K).homology (-(i : ℤ)) :=
  (torModuleComm i M N).toModuleIso ≪≫ torModuleIsoCochain N hK i

/-- 代数へ係数変更した第1変数の分解を、有限近似で使う順序の通常 Tor と比較する。 -/
noncomputable def ordinaryTorIsoLeft {T : Type u} [CommRing T] [Algebra R T]
    (M : Type u) [AddCommGroup M] [Module R M]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : IsResolutionOf K (ModuleCat.of R M)) (i : ℕ) :
    ((ModuleCat.restrictScalars (algebraMap R T)).obj
      ((baseChange (algebraMap R T) K).homology (-(i : ℤ)))) ≃ₗ[R] TorModule R i M T :=
  (ordinaryTorIso M K hK i).trans (torModuleComm i T M)

/-- 代数係数の Tor を基底環の通常の長さで測ると、有限近似で使う変数順と一致する。
代数側の線形性を変数交換に要求せず、係数制限した同値を使う。 -/
lemma length_restrictScalars_torAlg_comm {T : Type u} [CommRing T] [Algebra R T]
    (M : Type u) [AddCommGroup M] [Module R M] (i : ℕ) :
    Module.length R ((ModuleCat.restrictScalars (algebraMap R T)).obj
      (ModuleCat.of T (TorAlg (algebraMap R T) i M))) =
      Module.length R (TorModule R i M T) := by
  let P := projectiveResolution (ModuleCat.of R M)
  let e := (ModuleCat.restrictScalars (algebraMap R T)).mapIso
    (torIsoCochain (algebraMap R T) (isResolutionOf_extRes P) i)
  exact (e.toLinearEquiv.trans
    (ordinaryTorIsoLeft M (extRes P) (isResolutionOf_extRes P) i)).length_eq

end SerrePositivity
