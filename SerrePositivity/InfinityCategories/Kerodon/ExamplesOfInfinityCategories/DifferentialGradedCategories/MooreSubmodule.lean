module

public import Mathlib.AlgebraicTopology.MooreComplex
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# 正規化 Moore 複体の項と具体的な部分加群

概要：単体的加群の正規化 Moore 複体の各項を、正の面の核の共通部分として具体化する。
方針：Subobject の因子分解の普遍性と ModuleCat の線形写像を使う。
規約：微分は d₀ であり、ここでは各項の同型を与える。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の正規化と切断 Hom 複体の比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped _root_.Simplicial

variable {R : Type u} [CommRing R]

/-- 概要：単体的加群の各次数で正の面の線形核の共通部分を取る。
方針：零次数は全体、正次数は正の面を Fin の succ で添字付ける。
規約：Mathlib の正規化 Moore 複体の定義と同じ面を消す。
使われ方：HA 1.3.1.12 の正規化の具体的な加群模型。 -/
def normalizedModuleSubmodule (W : SimplicialObject (ModuleCat.{u} R)) :
    ∀ n : ℕ, Submodule R (W.obj (Opposite.op ⦋n⦌))
  | 0 => ⊤
  | n + 1 => ⨅ j : Fin (n + 1), LinearMap.ker (W.δ j.succ).hom

/-- 概要：Moore 正規化の包含と任意の正の面の合成は零である。
方針：核の共通部分の包含を対応する核へ因子分解する。
規約：零番目の面は含めない。
使われ方：HA 1.3.1.12 の抽象的正規化から具体的部分加群への写像。 -/
lemma moore_positiveFace_zero (W : SimplicialObject (ModuleCat.{u} R))
    (n : ℕ) (j : Fin (n + 1)) :
    (AlgebraicTopology.NormalizedMooreComplex.objX W (n + 1)).arrow ≫ W.δ j.succ = 0 := by
  dsimp only [AlgebraicTopology.NormalizedMooreComplex.objX]
  rw [← Subobject.factorThru_arrow _ _
    (Subobject.finset_inf_arrow_factors Finset.univ _ j (Finset.mem_univ _)),
    Category.assoc, kernelSubobject_arrow_comp, comp_zero]

/-- 概要：Moore 正規化の各項から具体的な正規化部分加群へ線形に送る。
方針：抽象的部分対象の包含を取り、正の面が零になることを添える。
規約：元の単体的加群への値は抽象的部分対象の包含の値と一致する。
使われ方：HA 1.3.1.12 の各項の自然な比較。 -/
def mooreToNormalizedModule (W : SimplicialObject (ModuleCat.{u} R)) (n : ℕ) :
    (AlgebraicTopology.NormalizedMooreComplex.objX W n : ModuleCat.{u} R) ⟶
      ModuleCat.of R (normalizedModuleSubmodule W n) :=
  ModuleCat.ofHom
    { toFun := fun s ↦ ⟨(AlgebraicTopology.NormalizedMooreComplex.objX W n).arrow s, by
        cases n with
        | zero => trivial
        | succ n =>
          apply (Submodule.mem_iInf _).mpr
          intro j
          exact congrArg (fun f ↦ f s) (moore_positiveFace_zero W n j)⟩
      map_add' := fun _ _ ↦ Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ ↦ Subtype.ext (map_smul _ _ _) }

/-- 概要：具体的な正規化部分加群の包含は Moore の正規化部分対象を経由する。
方針：全ての正の面の核への因子分解を共通部分へまとめる。
規約：具体的な部分加群の所属条件だけを用いる。
使われ方：HA 1.3.1.12 の具体的正規化から抽象的正規化への逆写像。 -/
lemma normalizedModule_subtype_factors (W : SimplicialObject (ModuleCat.{u} R)) (n : ℕ) :
    (AlgebraicTopology.NormalizedMooreComplex.objX W n).Factors
      (ModuleCat.ofHom (normalizedModuleSubmodule W n).subtype) := by
  cases n with
  | zero => exact Subobject.top_factors _
  | succ n =>
    apply (Subobject.finset_inf_factors _).mpr
    intro j _
    apply kernelSubobject_factors
    apply ConcreteCategory.hom_ext
    intro f
    exact (Submodule.mem_iInf _).mp f.property j

/-- 概要：Moore 正規化の各項は具体的な正の面の核の共通部分と同型である。
方針：具体的包含の因子分解を逆射とし、二つの包含の単射性で両逆則を証明する。
規約：任意の単体的加群と全ての次数で成立する。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の正規化複体の各項の計算。 -/
def mooreNormalizedModuleIso (W : SimplicialObject (ModuleCat.{u} R)) (n : ℕ) :
    (AlgebraicTopology.NormalizedMooreComplex.objX W n : ModuleCat.{u} R) ≅
      ModuleCat.of R (normalizedModuleSubmodule W n) where
  hom := mooreToNormalizedModule W n
  inv := (AlgebraicTopology.NormalizedMooreComplex.objX W n).factorThru
    (ModuleCat.ofHom (normalizedModuleSubmodule W n).subtype)
    (normalizedModule_subtype_factors W n)
  hom_inv_id := by
    apply (cancel_mono (AlgebraicTopology.NormalizedMooreComplex.objX W n).arrow).mp
    simp only [Category.assoc, Subobject.factorThru_arrow, Category.id_comp]
    rfl
  inv_hom_id := by
    have : Mono (ModuleCat.ofHom (normalizedModuleSubmodule W n).subtype) :=
      (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
    apply (cancel_mono (ModuleCat.ofHom (normalizedModuleSubmodule W n).subtype)).mp
    change _ ≫ ((mooreToNormalizedModule W n) ≫
      ModuleCat.ofHom (normalizedModuleSubmodule W n).subtype) = _
    change _ ≫ (AlgebraicTopology.NormalizedMooreComplex.objX W n).arrow = _
    rw [Subobject.factorThru_arrow, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
