module

public import SerrePositivity.CommutativeAlgebra.ResidueFieldExtension.Glue
public import SerrePositivity.CommutativeAlgebra.ResidueFieldExtension.Limit
public import SerrePositivity.CommutativeAlgebra.Adic.Noetherian
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Tensor
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Algebra

/-! # 任意の剰余体拡大の平坦局所拡大による実現

## 概要

局所環 `B` と、剰余体 `k = B/m_B` 上の任意の体 `K` に対し、平坦局所拡大 `B → C` で `m_B C = m_C`、
剰余体が `k` 上 `K` と同型なものがある（`exists_flat_local_extension_of_residueField`。EGA 0_III 10.3.1、
Bourbaki AC IX §2 の gonflement）。`B` が Noether なら `C` を完備 Noether 局所環にとれる
（`exists_complete_flat_local_extension_of_residueField`）。

## 方針

`K` の生成元を整列させ（`exists_residueField_generatorDiagram`）、両立する履歴
（`ResidueFieldExtension/Glue`）を全添字で貼り合わせた図式の直極限をとる。完備版は、`m_B C` 進完備化が
Noether で、各冪商が平坦で剰余体を保つことから従う（`exists_complete_flat_local_extension_of_noetherian_base`）。

## 規約

存在定理として述べる。体拡大の有限性・分離性・完全性は仮定しない。最初の主張に Noether 性は要らない。

## 使われ方

`Inputs/ResidueFieldExtension` の入口。Mathlib への提出候補（mathlib-upstream の G8）。
-/

@[expose] public noncomputable section

universe u v w

namespace SerrePositivity

section GeneralExtension

open IsLocalRing
variable {B K : Type u} [CommRing B] [IsLocalRing B] [Field K]
variable [Algebra (ResidueField B) K] [Algebra B K] [IsScalarTower B (ResidueField B) K]

/-- 整列した生成元の全体上に、実際の平坦局所代数の図式を構成する。 -/
theorem exists_residueField_generatorDiagram [LinearOrder K]
    (wf : WellFounded ((· < ·) : K → K → Prop)) :
    ∃ D : LocalAlgebraDiagram B K K,
      IsResidueFieldDiagram D (residueGeneratorAfter (ResidueField B) K) := by
  obtain ⟨s, hs⟩ := exists_coherent_residueFieldHistories (B := B) wf
  let hq := fun j k (h : j < k) ↦ (hs k).2 j h
  exact ⟨localAlgebraGlueAll s hq,
    residueFieldDiagramGlueAll_spec (residueGeneratorAfter (ResidueField B) K)
      s hq (fun j ↦ (hs j).1)⟩

omit [Algebra B K] [IsScalarTower B (ResidueField B) K] in
/-- 任意の指定剰余体拡大を、同じ宇宙の平坦局所B代数で実現する。
Noether性・完備性・体拡大の有限生成性は仮定しない。 -/
theorem exists_flat_local_extension_of_residueField :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      Module.Flat B C ∧ (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧
      ∃ e : ResidueField C ≃+* K,
        ∀ x, e (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x := by
  classical
  let : Algebra B K := ((algebraMap (ResidueField B) K).comp (residue B)).toAlgebra
  let : IsScalarTower B (ResidueField B) K := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  obtain ⟨ord, hwf⟩ := exists_residueGeneratorOrder K
  let : LinearOrder K := ord
  let : WellFoundedLT K := hwf
  obtain ⟨D, hD⟩ := exists_residueField_generatorDiagram (B := B) (K := K) wellFounded_lt
  let : DirectedSystem D.obj (D.map · · ·) := hD.1
  let : ∀ j, Module.Flat B (D.obj j) := hD.2.2.2.1
  apply exists_flat_local_extension_of_directed_system D.obj D.map hD.2.1
    hD.2.2.2.2.1 D.target hD.2.2.1
  intro x
  have hx : x ∈ Set.range (D.target x) := by
    rw [hD.2.2.2.2.2 x]
    exact residueGeneratorAfter_cover (ResidueField B) K x
  obtain ⟨y, hy⟩ := hx
  exact ⟨x, y, hy⟩

end GeneralExtension

section GeneralCompletion

open IsLocalRing

/-- 構成する完備化Cそのものについて、Noether性・完備性・剰余体・冪商を確認する。
存在定理からCの由来を推測せず、同じCに共通の平坦性を適用できる入口。 -/
theorem adicCompletion_local_residue_properties
    (B S K : Type u) [CommRing B] [IsLocalRing B]
    [CommRing S] [IsLocalRing S] [Algebra B S]
    [IsLocalHom (algebraMap B S)] [Module.Flat B S]
    [Field K] [Algebra (ResidueField B) K]
    (hB : (maximalIdeal B).FG)
    (hmax : (maximalIdeal B).map (algebraMap B S) = maximalIdeal S)
    (e : ResidueField S ≃+* K)
    (he : ∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x) :
    let hS : (maximalIdeal S).FG := hmax ▸ hB.map (algebraMap B S)
    let C := AdicCompletion (maximalIdeal S) S
    letI : IsLocalRing C := AdicCompletion.isLocalRing_of_fg hS
    letI : IsLocalHom (algebraMap S C) := AdicCompletion.algebraMap_isLocalHom_of_fg hS
    letI : IsLocalHom (algebraMap B C) := by
      rw [IsScalarTower.algebraMap_eq B S C]
      infer_instance
    IsNoetherianRing C ∧ IsAdicComplete (maximalIdeal C) C ∧
      (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧ (maximalIdeal C).FG ∧
      (∀ n : ℕ, Module.Flat (B ⧸ ((maximalIdeal B) ^ n))
        (C ⧸ ((maximalIdeal B) ^ n).map (algebraMap B C))) ∧
      ∃ eC : ResidueField C ≃+* K,
        ∀ x, eC (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x := by
  have hS : (maximalIdeal S).FG := hmax ▸ hB.map (algebraMap B S)
  let C := AdicCompletion (maximalIdeal S) S
  let : IsLocalRing C := AdicCompletion.isLocalRing_of_fg hS
  let : IsLocalHom (algebraMap S C) := AdicCompletion.algebraMap_isLocalHom_of_fg hS
  let : IsLocalHom (algebraMap B C) := by
    rw [IsScalarTower.algebraMap_eq B S C]
    infer_instance
  let : IsAdicComplete (maximalIdeal C) C := AdicCompletion.isAdicComplete_of_fg hS
  have hcmax : (maximalIdeal B).map (algebraMap B C) = maximalIdeal C := by
    rw [IsScalarTower.algebraMap_eq B S C, ← Ideal.map_map, hmax]
    exact (AdicCompletion.maximalIdeal_eq_map_of_fg hS).symm
  have hcFG : (maximalIdeal C).FG := hcmax ▸ hB.map (algebraMap B C)
  let : IsNoetherianRing C := isNoetherianRing_of_complete_local_of_fg C hcFG
  refine ⟨inferInstance, inferInstance, hcmax, hcFG, ?_,
    adicCompletionTargetResidueEquiv hS e, ?_⟩
  · intro n
    exact Eq.mp (congrArg (fun J : Ideal S ↦
      Module.Flat (B ⧸ ((maximalIdeal B) ^ n))
        (AdicCompletion J S ⧸ ((maximalIdeal B) ^ n).map
          (algebraMap B (AdicCompletion J S)))) hmax)
      (adicCompletionBasePowQuotient_flat (S := S) (maximalIdeal B) hB n)
  · exact adicCompletionTargetResidueEquiv_base_map hS e he

/-- 有限生成な基底の極大イデアルを持つ平坦局所拡大を完備化する。
元の拡大環SのNoether性を要求しない。 -/
theorem exists_complete_local_extension_with_flat_quotients
    (B S K : Type u) [CommRing B] [IsLocalRing B]
    [CommRing S] [IsLocalRing S] [Algebra B S]
    [IsLocalHom (algebraMap B S)] [Module.Flat B S]
    [Field K] [Algebra (ResidueField B) K]
    (hB : (maximalIdeal B).FG)
    (hmax : (maximalIdeal B).map (algebraMap B S) = maximalIdeal S)
    (e : ResidueField S ≃+* K)
    (he : ∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C)
      (_ : IsAdicComplete (maximalIdeal C) C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧ (maximalIdeal C).FG ∧
      (∀ n : ℕ, Module.Flat (B ⧸ ((maximalIdeal B) ^ n))
        (C ⧸ ((maximalIdeal B) ^ n).map (algebraMap B C))) ∧
      ∃ eC : ResidueField C ≃+* K,
        ∀ x, eC (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x := by
  have hS : (maximalIdeal S).FG := hmax ▸ hB.map (algebraMap B S)
  let C := AdicCompletion (maximalIdeal S) S
  let : IsLocalRing C := AdicCompletion.isLocalRing_of_fg hS
  let : IsLocalHom (algebraMap S C) := AdicCompletion.algebraMap_isLocalHom_of_fg hS
  let : IsLocalHom (algebraMap B C) := by
    rw [IsScalarTower.algebraMap_eq B S C]
    infer_instance
  obtain ⟨hNoeth, hComplete, hcmax, hcFG, hquot, eC, heC⟩ :=
    adicCompletion_local_residue_properties B S K hB hmax e he
  exact ⟨C, inferInstance, inferInstance, hNoeth, hComplete, inferInstance, inferInstance,
    hcmax, hcFG, hquot, eC, heC⟩

/-- Noether基底上の平坦局所拡大の具体的な完備化に、共通の代数版の平坦性を適用する。
中間環SのNoether性や基底Bの完備性は要求しない。 -/
theorem exists_complete_flat_local_extension_of_noetherian_base
    (B S K : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [CommRing S] [IsLocalRing S] [Algebra B S]
    [IsLocalHom (algebraMap B S)] [Module.Flat B S]
    [Field K] [Algebra (ResidueField B) K]
    (hmax : (maximalIdeal B).map (algebraMap B S) = maximalIdeal S)
    (e : ResidueField S ≃+* K)
    (he : ∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C)
      (_ : IsAdicComplete (maximalIdeal C) C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      Module.Flat B C ∧ (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧
      ∃ eC : ResidueField C ≃+* K,
        ∀ x, eC (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x := by
  have hB := (maximalIdeal B).fg_of_isNoetherianRing
  have hS : (maximalIdeal S).FG := hmax ▸ hB.map (algebraMap B S)
  let C := AdicCompletion (maximalIdeal S) S
  let : IsLocalRing C := AdicCompletion.isLocalRing_of_fg hS
  let : IsLocalHom (algebraMap S C) := AdicCompletion.algebraMap_isLocalHom_of_fg hS
  let : IsLocalHom (algebraMap B C) := by
    rw [IsScalarTower.algebraMap_eq B S C]
    infer_instance
  obtain ⟨hNoeth, hComplete, hcmax, hcFG, hquot, eC, heC⟩ :=
    adicCompletion_local_residue_properties B S K hB hmax e he
  have hFlat : Module.Flat B C := Eq.mp
    (congrArg (fun J : Ideal S ↦ Module.Flat B (AdicCompletion J S)) hmax)
    (flat_adicCompletion_algebra_of_flat (S := S) (maximalIdeal B))
  exact ⟨C, inferInstance, inferInstance, hNoeth, hComplete, inferInstance, inferInstance,
    hFlat, hcmax, eC, heC⟩

/-- 任意の剰余体拡大を、同じ宇宙の完備Noether平坦局所拡大で実現する。
基底の完備性や体拡大の有限性・分離性・完全性は仮定しない。 -/
theorem exists_complete_flat_local_extension_of_residueField
    (B K : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Field K] [Algebra (ResidueField B) K] :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C)
      (_ : IsAdicComplete (maximalIdeal C) C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      Module.Flat B C ∧ (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧
      ∃ eC : ResidueField C ≃+* K,
        ∀ x, eC (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x := by
  obtain ⟨S, sRing, sLocal, sAlg, sHom, sFlat, hmax, e, he⟩ :=
    exists_flat_local_extension_of_residueField (B := B) (K := K)
  exact exists_complete_flat_local_extension_of_noetherian_base B S K hmax e he

end GeneralCompletion

end SerrePositivity
