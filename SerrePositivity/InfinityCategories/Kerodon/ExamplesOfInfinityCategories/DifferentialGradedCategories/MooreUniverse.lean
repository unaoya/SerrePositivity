module

public import Mathlib.AlgebraicTopology.MooreComplex
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.Functor
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

universe u v w

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped _root_.Simplicial

variable {R : Type u} [CommRing R]

/-- 概要：単体的加群の各次数で正の面の線形核の共通部分を取る。
方針：零次数は全体、正次数は正の面を Fin の succ で添字付ける。
規約：Mathlib の正規化 Moore 複体の定義と同じ面を消す。
使われ方：HA 1.3.1.12 の正規化の具体的な加群模型。 -/
def mooreKernelModule (W : SimplicialObject (ModuleCat.{v} R)) :
    ∀ n : ℕ, Submodule R (W.obj (Opposite.op ⦋n⦌))
  | 0 => ⊤
  | n + 1 => ⨅ j : Fin (n + 1), LinearMap.ker (W.δ j.succ).hom

/-- 概要：Moore 正規化の包含と任意の正の面の合成は零である。
方針：核の共通部分の包含を対応する核へ因子分解する。
規約：零番目の面は含めない。
使われ方：HA 1.3.1.12 の抽象的正規化から具体的部分加群への写像。 -/
lemma mooreKernel_positiveFace_zero (W : SimplicialObject (ModuleCat.{v} R))
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
def mooreKernelMap (W : SimplicialObject (ModuleCat.{v} R)) (n : ℕ) :
    (AlgebraicTopology.NormalizedMooreComplex.objX W n : ModuleCat.{v} R) ⟶
      ModuleCat.of R (mooreKernelModule W n) :=
  ModuleCat.ofHom
    { toFun := fun s ↦ ⟨(AlgebraicTopology.NormalizedMooreComplex.objX W n).arrow s, by
        cases n with
        | zero => trivial
        | succ n =>
          apply (Submodule.mem_iInf _).mpr
          intro j
          exact congrArg (fun f ↦ f s) (mooreKernel_positiveFace_zero W n j)⟩
      map_add' := fun _ _ ↦ Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ ↦ Subtype.ext (map_smul _ _ _) }

/-- 概要：具体的な正規化部分加群の包含は Moore の正規化部分対象を経由する。
方針：全ての正の面の核への因子分解を共通部分へまとめる。
規約：具体的な部分加群の所属条件だけを用いる。
使われ方：HA 1.3.1.12 の具体的正規化から抽象的正規化への逆写像。 -/
lemma mooreKernel_subtype_factors (W : SimplicialObject (ModuleCat.{v} R)) (n : ℕ) :
    (AlgebraicTopology.NormalizedMooreComplex.objX W n).Factors
      (ModuleCat.ofHom (mooreKernelModule W n).subtype) := by
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
def mooreKernelIso (W : SimplicialObject (ModuleCat.{v} R)) (n : ℕ) :
    (AlgebraicTopology.NormalizedMooreComplex.objX W n : ModuleCat.{v} R) ≅
      ModuleCat.of R (mooreKernelModule W n) where
  hom := mooreKernelMap W n
  inv := (AlgebraicTopology.NormalizedMooreComplex.objX W n).factorThru
    (ModuleCat.ofHom (mooreKernelModule W n).subtype)
    (mooreKernel_subtype_factors W n)
  hom_inv_id := by
    apply (cancel_mono (AlgebraicTopology.NormalizedMooreComplex.objX W n).arrow).mp
    simp only [Category.assoc, Subobject.factorThru_arrow, Category.id_comp]
    rfl
  inv_hom_id := by
    have : Mono (ModuleCat.ofHom (mooreKernelModule W n).subtype) :=
      (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
    apply (cancel_mono (ModuleCat.ofHom (mooreKernelModule W n).subtype)).mp
    change _ ≫ ((mooreKernelMap W n) ≫
      ModuleCat.ofHom (mooreKernelModule W n).subtype) = _
    change _ ≫ (AlgebraicTopology.NormalizedMooreComplex.objX W n).arrow = _
    rw [Subobject.factorThru_arrow, Category.id_comp]

/-- 概要：Moore の包含で戻した微分は零番目の面である。
方針：共通核への因子分解を包含で戻す。
規約：係数環と加群の宇宙は独立。使われ方：宇宙持ち上げとの微分比較。 -/
lemma mooreKernel_d_arrow (W : SimplicialObject (ModuleCat.{v} R)) (n : ℕ) :
    ((normalizedMooreComplex (ModuleCat.{v} R)).obj W).d (n + 1) n ≫
      (NormalizedMooreComplex.objX W n).arrow =
        (NormalizedMooreComplex.objX W (n + 1)).arrow ≫ W.δ 0 := by
  rw [normalizedMooreComplex_objD]
  cases n with
  | zero => simp [NormalizedMooreComplex.objD, Category.assoc]
  | succ n =>
    dsimp only [NormalizedMooreComplex.objD]
    rw [Subobject.factorThru_arrow]

/-- 概要：宇宙持ち上げは Moore の具体的な共通核を保つ。
方針：ULift の down と up を核の元へ制限する。
規約：全ての正の面を同時に消す。使われ方：正規化と宇宙持ち上げの交換。 -/
def mooreKernelUliftEquiv (W : SimplicialObject (ModuleCat.{v} R)) (n : ℕ) :
    mooreKernelModule (W ⋙ ModuleCat.uliftFunctor.{w} R) n ≃ₗ[R]
      ULift.{w} (mooreKernelModule W n) where
  toFun s := ULift.up ⟨s.val.down, by
    cases n with
    | zero => trivial
    | succ n =>
      apply (Submodule.mem_iInf _).2
      intro j
      exact congrArg ULift.down ((Submodule.mem_iInf _).1 s.property j)⟩
  invFun s := ⟨ULift.up s.down.val, by
    cases n with
    | zero => trivial
    | succ n =>
      apply (Submodule.mem_iInf _).2
      intro j
      exact congrArg ULift.up ((Submodule.mem_iInf _).1 s.down.property j)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 概要：Moore 正規化の各項は加群の宇宙持ち上げと交換する。
方針：抽象的部分対象を具体的共通核で比較する。
規約：加群の線形同型。使われ方：正規化の複体の交換同型。 -/
def mooreUliftTermIso (W : SimplicialObject (ModuleCat.{v} R)) (n : ℕ) :
    ((normalizedMooreComplex (ModuleCat.{max v w} R)).obj
      (W ⋙ ModuleCat.uliftFunctor.{w} R)).X n ≅
      (ModuleCat.uliftFunctor.{w} R).obj (((normalizedMooreComplex (ModuleCat.{v} R)).obj W).X n) :=
  mooreKernelIso _ n ≪≫ (mooreKernelUliftEquiv.{u, v, w} W n).toModuleIso ≪≫
    (ModuleCat.uliftFunctor.{w} R).mapIso (mooreKernelIso W n).symm

/-- 概要：各項の宇宙比較は元の単体への包含と可換である。
方針：具体的共通核への同型とその逆の包含を計算する。
規約：両辺は同じ ULift 加群への射。使われ方：微分の可換性。 -/
lemma mooreUliftTermIso_arrow (W : SimplicialObject (ModuleCat.{v} R)) (n : ℕ) :
    (mooreUliftTermIso.{u, v, w} W n).hom ≫
      (ModuleCat.uliftFunctor.{w} R).map (NormalizedMooreComplex.objX W n).arrow =
        (NormalizedMooreComplex.objX (W ⋙ ModuleCat.uliftFunctor.{w} R) n).arrow := by
  have hi : (mooreKernelIso W n).inv ≫ (NormalizedMooreComplex.objX W n).arrow =
      ModuleCat.ofHom (mooreKernelModule W n).subtype := by
    dsimp only [mooreKernelIso]
    rw [Subobject.factorThru_arrow]
  simp only [mooreUliftTermIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc,
    ← Functor.map_comp, hi]
  rfl

/-- 概要：Moore 正規化は複体として宇宙持ち上げと交換する。
方針：各項の同型を元の単体への包含で検査し、微分 d₀ の可換性を証明する。
規約：標準の Mathlib 正規化を使う。使われ方：実際の pinched Hom の大きい宇宙への比較。 -/
def mooreUliftIso (W : SimplicialObject (ModuleCat.{v} R)) :
    (normalizedMooreComplex (ModuleCat.{max v w} R)).obj (W ⋙ ModuleCat.uliftFunctor.{w} R) ≅
      ((ModuleCat.uliftFunctor.{w} R).mapHomologicalComplex (.down ℕ)).obj
        ((normalizedMooreComplex (ModuleCat.{v} R)).obj W) :=
  HomologicalComplex.Hom.isoOfComponents (mooreUliftTermIso.{u, v, w} W) (by
    intro i j hij
    have hi : i = j + 1 := by simpa using hij.symm
    subst hi
    apply (cancel_mono ((ModuleCat.uliftFunctor.{w} R).map
      (NormalizedMooreComplex.objX W j).arrow)).1
    change (mooreUliftTermIso W (j + 1)).hom ≫
      (ModuleCat.uliftFunctor.{w} R).map (((normalizedMooreComplex _).obj W).d (j + 1) j) ≫
      (ModuleCat.uliftFunctor.{w} R).map _ = _
    rw [← Functor.map_comp, mooreKernel_d_arrow, Functor.map_comp,
      ← Category.assoc, mooreUliftTermIso_arrow, Category.assoc,
      mooreUliftTermIso_arrow, mooreKernel_d_arrow]
    rfl)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
