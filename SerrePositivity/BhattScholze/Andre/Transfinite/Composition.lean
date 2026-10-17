module

public import SerrePositivity.HomologicalAlgebra.TorAcyclicBaseChangeComparison
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatPowerTorsion
public import SerrePositivity.HomologicalAlgebra.ModuleScalarExtensionAnnihilator
/-! # 完全平坦・完全忠実平坦な環準同型の合成

BS Thm 7.14（著者版 p.61）の超限塔で、各後続段から初期環までの性質を保つための一般論。
イデアルで消える任意の試験加群をスカラー拡大し、Tor と忠実性を二段階で検査する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.BhattScholze.Andre.Transfinite
open SerrePositivity CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
/-- ## 概要
スカラー制限で記述した二つの完全平坦写像の合成は完全平坦。
BS Thm 7.14（著者版 p.61）の塔の後続段に用いる補助命題。

## 方針
試験加群の Tor 非輪状性から実際の底変換 Tor 比較を適用し、拡大後の試験加群には
拡張イデアルが零として作用することを使う。

## 規約
元の合成環準同型の作用と、二段階のスカラー制限の作用を線形同型で明示的に比較する。

## 使われ方
toAlgebra を使う公開版の証明に使う。
-/
private theorem completelyFlat_comp_restricted {R B C : Type u}
    [CommRing R] [CommRing B] [CommRing C]
    (φ : R →+* B) (ψ : B →+* C) (I : Ideal R)
    (hB : IsCompletelyFlat I (baseChangeScalarModule φ))
    (hC : IsCompletelyFlat (I.map φ) (baseChangeScalarModule ψ)) :
    IsCompletelyFlat I (baseChangeScalarModule (ψ.comp φ)) := by
  intro N _ _ hN
  apply (isConcentratedInDegreeZero_derivedTensor_iff _ N).mpr
  intro i hi
  let N' := ModuleCat.of R N
  have hTor : scalarExtensionTorVanishing φ N' := hB N hN
  let M := (ModuleCat.extendScalars φ).obj N'
  have hAnn : I.map φ ≤ Module.annihilator B M := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    exact Module.mem_annihilator.mpr (scalarExtension_annihilated φ r N' (hN r hr))
  have hMI : ∀ r ∈ I.map φ, ∀ x : M, r • x = 0 :=
    fun r hr x ↦ Module.mem_annihilator.mp (hAnn hr) x
  have hz := hC M hMI i hi
  have hz' : IsZero (((Tor (ModuleCat B) i).obj (baseChangeScalarModule ψ)).obj M) := hz
  have hzR := (ModuleCat.restrictScalars φ).map_isZero hz'
  have he := torAcyclicBaseChangeIso φ N' hTor (baseChangeScalarModule ψ) i
  have hzOriginal := hzR.of_iso he
  let E : (baseChangeScalarModule (ψ.comp φ)) ≃ₗ[R]
      ((ModuleCat.restrictScalars φ).obj (baseChangeScalarModule ψ)) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hzFinal := hzOriginal.of_iso (((Tor (ModuleCat R) i).mapIso E.toModuleIso).app N')
  exact ModuleCat.subsingleton_of_isZero hzFinal

/-- ## 概要
I 完全平坦な R → B と IB 完全平坦な B → C の合成は I 完全平坦。
BS Thm 7.14（著者版 p.61）の超限塔の後続段で使用する。

## 方針
試験加群の底変換と Tor 比較による補助命題を、元の環準同型の toAlgebra 作用で適用する。

## 規約
p 正則性・完備性・有限生成性を要求しない。拡張イデアルは I.map φ。

## 使われ方
各段から初期環への完全平坦性を、後続段へ合成して運ぶ。
-/
theorem isCompletelyFlat_comp {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
    (φ : R →+* B) (ψ : B →+* C) (I : Ideal R)
    (hB : letI := φ.toAlgebra; IsCompletelyFlat I B)
    (hC : letI := ψ.toAlgebra; IsCompletelyFlat (I.map φ) C) :
    letI := (ψ.comp φ).toAlgebra; IsCompletelyFlat I C := by
  exact completelyFlat_comp_restricted φ ψ I hB hC

/-- ## 概要
通常剰余テンソルが忠実平坦なら、I で消える試験加群の零性は元のテンソルで検出できる。
BS Thm 7.14（著者版 p.61）の合成の忠実性に用いる一般補題。

## 方針
試験加群に R/I 作用を与え、通常テンソルの底変換消去同型を通して忠実平坦性を適用する。

## 規約
P 自身の完全平坦性や通常平坦性は不要。N は I の元すべてで消える。

## 使われ方
二段の拡大後に試験加群が零になれば、順に元へ戻して零性を検出する。
-/
theorem subsingleton_of_annihilated_of_residueTensor {R : Type u} [CommRing R] (I : Ideal R)
    (P : Type u) [AddCommGroup P] [Module R P]
    (hP : Module.FaithfullyFlat (R ⧸ I) ((R ⧸ I) ⊗[R] P))
    (N : Type u) [AddCommGroup N] [Module R N]
    (hN : ∀ r ∈ I, ∀ x : N, r • x = 0)
    (hTensor : Subsingleton (N ⊗[R] P)) : Subsingleton N := by
  let hNt : Module.IsTorsionBySet R N (I : Set R) := fun {x} {r} ↦ hN r r.property x
  let := hNt.module
  have : IsScalarTower R (R ⧸ I) N := inferInstance
  let := hP
  let e := AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (R ⧸ I) N P
  have : Subsingleton (N ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] P)) := e.injective.subsingleton
  exact Module.FaithfullyFlat.rTensor_reflects_triviality (R ⧸ I) ((R ⧸ I) ⊗[R] P) N

/-- ## 概要
I 完全忠実平坦な R → B と IB 完全忠実平坦な B → C の合成は I 完全忠実平坦。
BS Thm 7.14（著者版 p.61）の塔の後続段で使う。

## 方針
完全平坦性を Tor の底変換で合成し、通常剰余テンソルの平坦性を得る。
忠実性は I で消える試験加群を二段階の忠実なテンソルで反映して証明する。

## 規約
I は任意。非零性・p 正則性・通常平坦性・完備性は不要。
環の作用はすべて指定した環準同型の toAlgebra。

## 使われ方
初期環から各段への p 完全忠実平坦性を、後続写像との合成で保つ。
-/
theorem isCompletelyFaithfullyFlat_comp {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
    (φ : R →+* B) (ψ : B →+* C) (I : Ideal R)
    (hB : letI := φ.toAlgebra; IsCompletelyFaithfullyFlat I B)
    (hC : letI := ψ.toAlgebra; IsCompletelyFaithfullyFlat (I.map φ) C) :
    letI := (ψ.comp φ).toAlgebra; IsCompletelyFaithfullyFlat I C := by
  let := φ.toAlgebra
  let := ψ.toAlgebra
  let := (ψ.comp φ).toAlgebra
  let : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  have hFlat : IsCompletelyFlat I C := completelyFlat_comp_restricted φ ψ I hB.1 hC.1
  refine ⟨hFlat, ?_⟩
  apply (Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality (R ⧸ I) _).mpr
  refine ⟨flat_residueTensor_of_completelyFlat I C hFlat, ?_⟩
  intro N _ _ hTensor
  let _ : Module R N := Module.compHom N (Ideal.Quotient.mk I)
  have : IsScalarTower R (R ⧸ I) N := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let e0 := AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (R ⧸ I) N C
  have : Subsingleton (N ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] C)) := hTensor
  have hNC : Subsingleton (N ⊗[R] C) := e0.symm.injective.subsingleton
  have : Subsingleton (C ⊗[R] N) := (TensorProduct.comm R C N).injective.subsingleton
  let M := B ⊗[R] N
  let e1 := (TensorProduct.comm B M C).trans
    (AlgebraTensorModule.cancelBaseChange R B B C N)
  have hMC : Subsingleton (M ⊗[B] C) := e1.injective.subsingleton
  have hNI : ∀ r ∈ I, ∀ x : N, r • x = 0 := by
    intro r hr x
    change Ideal.Quotient.mk I r • x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]
  have hAnn : I.map φ ≤ Module.annihilator B M := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    apply Module.mem_annihilator.mpr
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b n =>
      change (r • b) ⊗ₜ[R] n = 0
      rw [TensorProduct.smul_tmul, hNI r hr, TensorProduct.tmul_zero]
    | add x y hx hy => rw [smul_add, hx, hy, zero_add]
  have hM : Subsingleton M := subsingleton_of_annihilated_of_residueTensor (I.map φ) C hC.2 M
    (fun r hr x ↦ Module.mem_annihilator.mp (hAnn hr) x) hMC
  have hNB : Subsingleton (N ⊗[R] B) := (TensorProduct.comm R N B).injective.subsingleton
  exact subsingleton_of_annihilated_of_residueTensor I B hB.2 N hNI hNB

/-- ## 概要
自然数 p に関する完全忠実平坦な二つの環準同型の合成は p 完全忠実平坦。
BS Thm 7.14（著者版 p.61）の後続段で step の出力を合成する入口。

## 方針
主イデアル (p) の環準同型による像が再び (p) であることから、一般の合成定理に帰着する。

## 規約
p の素数性はこの保存には不要。各作用は指定した環準同型の toAlgebra。

## 使われ方
元の step と同じ (p) の型を、拡張イデアルの型に変更せずに使う。
-/
theorem isCompletelyFaithfullyFlat_natCast_comp {R B C : Type u}
    [CommRing R] [CommRing B] [CommRing C]
    (φ : R →+* B) (ψ : B →+* C) (p : ℕ)
    (hB : letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) B)
    (hC : letI := ψ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : B)}) C) :
    letI := (ψ.comp φ).toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) C := by
  apply isCompletelyFaithfullyFlat_comp φ ψ (Ideal.span {(p : R)}) hB
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hC

end SerrePositivity.BhattScholze.Andre.Transfinite
