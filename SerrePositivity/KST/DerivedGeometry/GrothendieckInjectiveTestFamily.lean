module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.DerivedGeometry.DiskEnvelopeInjectivity
public import SerrePositivity.KST.DerivedGeometry.GrothendieckTestQuasiIso

/-!
概要：非輪状試験族への直交性と各項 injectivity を同時に持つ単射準同型を構成する。
方針：生成対象の部分対象の二項複体を小さい添字へ縮小し、試験族へ加える。
規約：小さい試験族だけへの直交性であり、まだ全 K-injective 性とはしない。
使われ方：Stacks 19.12.3・19.12.6、TT §3・§8、Toën §3.2 の非有界分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits ZeroObject
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {σ : Type w}

/--
概要：生成対象の部分対象と次数で添字付けた小さい二項複体の族。
方針：部分対象の型の universe 縮小を使う。
規約：縮小前の全ての部分対象が添字の像に含まれる。
使われ方：Stacks 19.12.6、TT §3 の各項 injectivity を強制する試験。
-/
def generatorDiskFamily (G : C) (s : ℤ × Shrink.{w} (Subobject G)) : CochainComplex C ℤ :=
  cochainDisk ((equivShrink (Subobject G)).symm s.2 : C) s.1

/--
概要：指定した非輪状試験族に直交する、各項 injective な複体への単射準同型が存在する。
方針：試験族と二項複体の和に small object factorization を適用し、各項を持ち上げで判定する。
規約：分解の存在も各項 injectivity も未証明フィールドで与えない。
使われ方：Stacks 19.12.3・19.12.6、TT §3・§8、Toën §3.2 の非有界分解の構成。
-/
lemma exists_mono_quasiIso_injective_test_orthogonal
    (A : σ → CochainComplex C ℤ) (hA : ∀ i, (A i).Acyclic) (M : CochainComplex C ℤ) :
    ∃ (N : CochainComplex C ℤ) (j : M ⟶ N), Mono j ∧ QuasiIso j ∧
      (∀ n, Injective (N.X n)) ∧
      ∀ (i : σ) (f : A i ⟶ N), Nonempty (Homotopy f 0) := by
  let G := separator C
  let B : σ ⊕ (ℤ × Shrink.{w} (Subobject G)) → CochainComplex C ℤ :=
    Sum.elim A (generatorDiskFamily G)
  have hB : ∀ i, (B i).Acyclic := by
    intro i
    cases i with
    | inl i => exact hA i
    | inr s => exact cochainDisk_acyclic _ _
  have hi : ∀ i, QuasiIso (termInjectiveEnvelopeι (B i)) := fun i =>
    quasiIso_of_acyclic (B i) _ _ (hB i) (adjacentBiproductComplex_acyclic _)
  obtain ⟨N, j, p, hjp, hj, hqj, hp⟩ :=
    smallMonoQuasiIsoFamily_exists_factorization (fun i => termInjectiveEnvelopeι (B i)) hi
      (0 : M ⟶ 0)
  have hp0 : p = (0 : N ⟶ 0) := Subsingleton.elim _ _
  rw [hp0] at hp
  refine ⟨N, j, hj, hqj, ?_, ?_⟩
  · apply injective_components_of_disk_envelope_lifting G (isSeparator_separator C) N
    intro S n
    have h := hp _ ⟨Sum.inr (n, equivShrink (Subobject G) S)⟩
    change HasLiftingProperty (termInjectiveEnvelopeι
      (cochainDisk ((equivShrink (Subobject G)).symm ((equivShrink (Subobject G)) S) : C) n))
      (0 : N ⟶ 0) at h
    rw [Equiv.symm_apply_apply] at h
    exact h
  · intro i f
    have : HasLiftingProperty (termInjectiveEnvelopeι (A i)) (0 : N ⟶ 0) :=
      hp _ ⟨Sum.inl i⟩
    exact ⟨homotopyZero_of_envelope_lifting (A i) N f⟩

end SerrePositivity.KST.DerivedGeometry

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.5.3" (partial := stronger-hyp) "仮定：有界な cochain 複体で、Quillen のモデル構造には十分な入射対象を要求。無界側の補題は Grothendieck 圏と小さい試験族を入力（Lean が強い：モデル圏は有界な場合に限定）。結論：有界側には scoped ModelCategory instance が実在し、余ファイブレーションはモノ、弱同値は準同型。無界側で得られるのは試験族に直交する入射複体へのモノ準同型（Lean が弱い：無界側の injective ModelCategory instance と左固有性・組合せ性は確認できない）。"] _root_.SerrePositivity.KST.DerivedGeometry.exists_mono_quasiIso_injective_test_orthogonal
