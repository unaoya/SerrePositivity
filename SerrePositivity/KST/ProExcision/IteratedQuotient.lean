module

public import SerrePositivity.KST.ProExcision.KoszulConeComparison

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

/-!
# 反復する通常商の標準射と核

概要：反復冪商を元の加群の一度の商へ同定するため、標準全射と核を計算する。
方針：一変数の商の合成の核は、元の核とスカラー像の和である。
規約：通常の加群の商であり、Noether 性や有限性は不要。
使われ方：KST Lemma 4.9・4.10 の通常の生成イデアルによる商との比較。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]

/-- 概要：任意の加群からスカラー商への標準全射。
方針：スカラー像の商写像を使う。
規約：スカラー零も許す。使われ方：KST Lemma 4.10 の通常商の標準射。 -/
def scalarQuotientπ (a : R) (M : ModuleCat.{u} R) :
    M ⟶ (scalarQuotientFunctor a).obj M :=
  ModuleCat.ofHom (a • (LinearMap.id : M →ₗ[R] M)).range.mkQ

/-- 概要：動く冪商への射影をレベル射にする。
方針：線形写像を商へ降ろす定義を使う。
規約：係数遷移と冪指数は同時に動く。
使われ方：KST Lemma 4.10 の反復通常商への自然な全射。 -/
def Tower.powerQuotientProjection (X : Tower (ModuleCat.{u} R)) (a : R) :
    LevelHom X (X.powerQuotient a) where
  app n := scalarQuotientπ (a ^ n) (X.obj n)
  naturality h := by rfl

/-- 概要：元の加群から全変数の反復冪商へのレベル射。
方針：列長について通常商への射影を合成する。
規約：空列の射は恒等射。使われ方：KST Lemma 4.10 の比較の標準性。 -/
def iteratedPowerQuotientProjection : ∀ {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R),
    LevelHom (Tower.constant M) (iteratedPowerQuotientTower z M)
  | 0, _, M => LevelHom.id (Tower.constant M)
  | e + 1, z, M => LevelHom.comp (iteratedPowerQuotientProjection (Fin.init z) M)
      ((iteratedPowerQuotientTower (Fin.init z) M).powerQuotientProjection (z (Fin.last e)))

/-- 概要：反復冪商への標準射は各段で全射。
方針：通常商への全射を列長について合成する。
規約：全射の切断は選ばない。使われ方：KST Lemma 4.10 の第一同型定理。 -/
theorem iteratedPowerQuotientProjection_surjective : ∀ {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} R) (n : ℕ),
    Function.Surjective ((iteratedPowerQuotientProjection z M).app n).hom
  | 0, _, _, _ => Function.surjective_id
  | e + 1, z, M, n =>
      (Submodule.mkQ_surjective _).comp
        (iteratedPowerQuotientProjection_surjective (Fin.init z) M n)

/-- 概要：全射の後にスカラー商を取ると、核は元の核とスカラー像の和。
方針：商で零となる元をスカラー倍へ持ち上げ、差を元の核へ戻す。
規約：元の写像の全射性が必要。使われ方：KST Lemma 4.10 の反復商の核の計算。 -/
theorem ker_comp_scalarQuotientπ (a : R) {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hf : Function.Surjective f.hom) :
    (f ≫ scalarQuotientπ a N).hom.ker =
      f.hom.ker ⊔ (a • (LinearMap.id : M →ₗ[R] M)).range := by
  ext x
  constructor
  · intro hx
    have hx' : f.hom x ∈ (a • (LinearMap.id : N →ₗ[R] N)).range :=
      (Submodule.Quotient.mk_eq_zero _).mp hx
    obtain ⟨y, hy⟩ := hx'
    obtain ⟨z, hz⟩ := hf y
    apply Submodule.mem_sup.mpr
    refine ⟨x - a • z, ?_, a • z, ⟨z, rfl⟩, sub_add_cancel _ _⟩
    change f.hom (x - a • z) = 0
    rw [map_sub, map_smul, hz]
    change f.hom x - a • y = 0
    exact sub_eq_zero.mpr hy.symm
  · intro hx
    obtain ⟨y, hy, _, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
    change (a • (LinearMap.id : N →ₗ[R] N)).range.mkQ (f.hom (y + a • z)) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨f.hom z, ?_⟩
    change a • f.hom z = f.hom (y + a • z)
    rw [map_add, map_smul, show f.hom y = 0 from hy, zero_add]

/-- 概要：有限列が生成する加群の部分加群。
方針：末尾変数のスカラー像を順に和へ加える。
規約：通常の生成イデアル倍との一致は別途示す。
使われ方：KST Lemma 4.10 の反復商の核の帰納的な表示。 -/
def parameterSubmodule : ∀ {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R), Submodule R M
  | 0, _, _ => ⊥
  | e + 1, z, M => parameterSubmodule (Fin.init z) M ⊔
      (z (Fin.last e) • (LinearMap.id : M →ₗ[R] M)).range

/-- 概要：反復冪商への標準全射の核は変数の冪が生成する部分加群。
方針：一変数の商の合成の核を列長について反復する。
規約：追加の有限性条件は不要。使われ方：KST Lemma 4.10 の一度の通常商との同定。 -/
theorem iteratedPowerQuotientProjection_ker : ∀ {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} R) (n : ℕ),
    ((iteratedPowerQuotientProjection z M).app n).hom.ker =
      parameterSubmodule (fun j ↦ z j ^ n) M
  | 0, _, _, _ => LinearMap.ker_id
  | e + 1, z, M, n => by
      change (((iteratedPowerQuotientProjection (Fin.init z) M).app n) ≫
        scalarQuotientπ (z (Fin.last e) ^ n) _).hom.ker = _
      rw [ker_comp_scalarQuotientπ _ _
        (iteratedPowerQuotientProjection_surjective (Fin.init z) M n),
        iteratedPowerQuotientProjection_ker]
      rfl

end SerrePositivity.KST.ProExcision
