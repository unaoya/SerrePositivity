module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.Semifree
public import Mathlib.LinearAlgebra.Basis.Basic

/-! # 高さ付き semibasis による semifree 複体の補助表現

概要：各次数の基底を自然数の高さで添字付け、微分が高さを下げることを記録する。
方針：有限な基底展開を使って高さで切った部分加群の微分閉性を示す。
規約：既存の `complexSemifree` の転送定義は変更しない。
使われ方：任意の射の cone に対する filtration の再構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S]

/-- 概要：微分が基底の自然数の高さを真に下げる semibasis。
方針：微分の基底展開の有限な台に対して降下条件を課す。
規約：各次数の基底の添字は加群と同じ宇宙に置く。
使われ方：semifree filtration との同値および cone の高さの構成。 -/
structure ComplexSemifreeBasis (P : Complex S) where
  Index : ℤ → Type u
  basis : ∀ k, Module.Basis (Index k) S (P.X k)
  height : ∀ k, Index k → ℕ
  lowering : ∀ (k : ℤ) (i : Index k) (j : Index (k + 1)),
    j ∈ ((basis (k + 1)).repr ((P.d k (k + 1)) (basis k i))).support →
      height (k + 1) j < height k i

namespace ComplexSemifreeBasis
variable {S} {P : Complex S} (B : ComplexSemifreeBasis S P)

/-- 概要：高さ n 以下の基底元で張る次数 k の部分加群。
方針：基底の部分集合の線形包を取る。規約：高さの上限は包含する。
使われ方：semifree filtration の各段の複体を構成する。 -/
def stageSubmodule (n : ℕ) (k : ℤ) : Submodule S (P.X k) :=
  Submodule.span S ((B.basis k) '' {i | B.height k i ≤ n})

/-- 概要：段への所属は基底展開の台の高さで判定できる。
方針：基底の部分集合の線形包に対する既存の判定を使う。
規約：台は有限集合。使われ方：微分閉性と網羅性の証明。 -/
theorem mem_stageSubmodule_iff (n : ℕ) (k : ℤ) (x : P.X k) :
    x ∈ B.stageSubmodule n k ↔
      ∀ i ∈ ((B.basis k).repr x).support, B.height k i ≤ n := by
  exact (B.basis k).mem_span_image

/-- 概要：高さの上限を増やすと段の部分加群も増える。
方針：生成する基底元の集合の包含を線形包へ移す。
規約：同じ次数で比較する。使われ方：filtration の遷移。 -/
theorem stageSubmodule_mono {n m : ℕ} (h : n ≤ m) (k : ℤ) :
    B.stageSubmodule n k ≤ B.stageSubmodule m k := by
  apply Submodule.span_mono
  exact Set.image_mono (fun _ hi => hi.trans h)

/-- 概要：任意の斉次要素はある有限の高さの段に属する。
方針：基底展開の有限な台に現れる高さの最大値を取る。
規約：空の台の最大値は零。使われ方：filtration の網羅性。 -/
theorem exists_mem_stageSubmodule (k : ℤ) (x : P.X k) :
    ∃ n, x ∈ B.stageSubmodule n k := by
  classical
  refine ⟨((B.basis k).repr x).support.sup (B.height k), ?_⟩
  apply (B.mem_stageSubmodule_iff _ _ _).mpr
  intro i hi
  exact Finset.le_sup hi

/-- 概要：第 n+1 段の微分は第 n 段に入る。
方針：要素を基底展開し、各微分の台に対する高さの降下を使う。
規約：余鎖微分は次数を一つ上げる。使われ方：各商の微分が零であること。 -/
theorem differential_mem_previous (n : ℕ) (k : ℤ) {x : P.X k}
    (hx : x ∈ B.stageSubmodule (n + 1) k) :
    (P.d k (k + 1)) x ∈ B.stageSubmodule n (k + 1) := by
  classical
  have hs := (B.mem_stageSubmodule_iff _ _ _).mp hx
  rw [← (B.basis k).linearCombination_repr x, Finsupp.linearCombination_apply,
    Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [map_smul]
  apply Submodule.smul_mem
  apply (B.mem_stageSubmodule_iff _ _ _).mpr
  intro j hj
  have hlow := B.lowering k i j hj
  have hhigh := hs i hi
  omega

/-- 概要：各高さの段は微分で閉じている。
方針：一つ上の段への包含と、微分が高さを下げることを使う。
規約：同じ高さの上限で始域と終域を切る。使われ方：段の複体の定義。 -/
theorem differential_mem_stage (n : ℕ) (k : ℤ) {x : P.X k}
    (hx : x ∈ B.stageSubmodule n k) :
    (P.d k (k + 1)) x ∈ B.stageSubmodule n (k + 1) :=
  B.differential_mem_previous n k (B.stageSubmodule_mono (Nat.le_succ n) k hx)

/-- 概要：高さで切った段に制限した微分。
方針：元の微分の定義域と値域を段の部分加群へ制限する。
規約：余鎖微分は次数を一つ上げる。使われ方：段の複体の構成。 -/
def stageDifferential (n : ℕ) (k : ℤ) :
    ModuleCat.of S (B.stageSubmodule n k) ⟶ ModuleCat.of S (B.stageSubmodule n (k + 1)) :=
  ModuleCat.ofHom (LinearMap.codRestrict _
    ((P.d k (k + 1)).hom.comp (B.stageSubmodule n k).subtype)
    (fun x => B.differential_mem_stage n k x.property))

/-- 概要：段の微分も二乗零である。
方針：包含の単射性で元の複体の二乗零に帰着する。
規約：包含の下で微分は元の微分そのもの。使われ方：段の複体の法則。 -/
theorem stageDifferential_squared (n : ℕ) (k : ℤ) :
    B.stageDifferential n k ≫ B.stageDifferential n (k + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (P.d (k + 1) (k + 1 + 1)) ((P.d k (k + 1)) x.val) = 0
  have h := congrArg (fun f : P.X k ⟶ P.X (k + 1 + 1) => f.hom x.val)
    (P.d_comp_d k (k + 1) (k + 1 + 1))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_zero, LinearMap.zero_apply] using h

/-- 概要：高さ n 以下の基底元で張られる部分複体。
方針：制限した微分とその二乗零から余鎖複体を作る。
規約：対象は各次数の部分加群。使われ方：semifree filtration の各段。 -/
def stageComplex (n : ℕ) : Complex S :=
  CochainComplex.of (fun k => ModuleCat.of S (B.stageSubmodule n k))
    (B.stageDifferential n) (B.stageDifferential_squared n)

/-- 概要：高さで切った部分複体の元の複体への包含。
方針：各次数の部分加群の包含は制限微分と可換する。
規約：複体の射として与える。使われ方：網羅的 filtration の cocone。 -/
def stageInclusion (n : ℕ) : B.stageComplex n ⟶ P :=
  CochainComplex.ofHom (fun k => ModuleCat.ofHom (B.stageSubmodule n k).subtype) (by
    intro k
    dsimp only [stageComplex]
    rw [CochainComplex.of_d]
    rfl)

/-- 概要：高さの上限の増大による段の間の複体の射。
方針：各次数で部分加群の包含を使う。
規約：上限の大小関係を明示する。使われ方：filtration の遷移と余極限。 -/
def stageMap {n m : ℕ} (h : n ≤ m) : B.stageComplex n ⟶ B.stageComplex m :=
  CochainComplex.ofHom
    (fun k => ModuleCat.ofHom (Submodule.inclusion (B.stageSubmodule_mono h k))) (by
      intro k
      dsimp only [stageComplex]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rfl)

/-- 概要：段の包含を経由しても元の複体への包含は変わらない。
方針：各次数で部分加群の包含の合成を計算する。
規約：比較する高さの順序を仮定する。使われ方：網羅的 cocone の整合性。 -/
theorem stageMap_inclusion {n m : ℕ} (h : n ≤ m) :
    B.stageMap h ≫ B.stageInclusion m = B.stageInclusion n := by
  apply HomologicalComplex.Hom.ext
  funext k
  rfl

/-- 概要：各段の各次数にも、対応する部分集合で添字付けた基底がある。
方針：元の基底の一次独立な部分族をその線形包の基底にする。
規約：添字は高さが上限以下の基底元。使われ方：自由な初期段と商の表示。 -/
def stageBasis (n : ℕ) (k : ℤ) :
    Module.Basis {i : B.Index k // B.height k i ≤ n} S (B.stageSubmodule n k) := by
  unfold stageSubmodule
  rw [Set.image_eq_range]
  exact Module.Basis.span ((B.basis k).linearIndependent.comp
      (fun i : {i : B.Index k // B.height k i ≤ n} => i.val) Subtype.val_injective)

/-- 概要：高さで切った部分複体を自然数上の図式にする。
方針：任意の n ≤ m に対応する包含を射に使う。
規約：比較射は部分加群の包含そのもの。使われ方：網羅性を余極限へ接続する。 -/
def stageDiagram : ℕ ⥤ Complex S where
  obj := B.stageComplex
  map f := B.stageMap (leOfHom f)
  map_id n := by
    apply HomologicalComplex.Hom.ext
    funext k
    rfl
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext k
    rfl

/-- 概要：各段の包含は元の複体を頂点とする cocone を定める。
方針：部分加群の包含の合成則を使う。
規約：頂点は元の複体。使われ方：semifree filtration の網羅性。 -/
def stageCocone : Limits.Cocone B.stageDiagram where
  pt := P
  ι :=
    { app := B.stageInclusion
      naturality _ _ f := by
        exact (B.stageMap_inclusion (leOfHom f)).trans (Category.comp_id _).symm }

/-- 概要：初期段の微分は零である。
方針：高さ零の基底元の微分には、より低い高さの台が存在し得ない。
規約：自然数の最小の高さを零とする。使われ方：初期段の自由 sphere 表示。 -/
theorem differential_eq_zero_on_stageZero (k : ℤ) {x : P.X k}
    (hx : x ∈ B.stageSubmodule 0 k) : (P.d k (k + 1)) x = 0 := by
  classical
  have hs := (B.mem_stageSubmodule_iff _ _ _).mp hx
  rw [← (B.basis k).linearCombination_repr x, Finsupp.linearCombination_apply,
    Finsupp.sum, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_smul]
  have hd : (P.d k (k + 1)) (B.basis k i) = 0 := by
    apply (B.basis (k + 1)).repr.injective
    apply Finsupp.ext
    intro j
    simp only [map_zero, Finsupp.zero_apply]
    by_contra hj
    have hlow := B.lowering k i j (Finsupp.mem_support_iff.mpr hj)
    have hhigh := hs i hi
    omega
  rw [hd, smul_zero]

end ComplexSemifreeBasis
end SerrePositivity.InfinityCategories.Project.DerivedCategories
