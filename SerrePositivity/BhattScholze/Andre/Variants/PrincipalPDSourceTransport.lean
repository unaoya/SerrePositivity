module

public import SerrePositivity.BhattScholze.Andre.Remark715.PrincipalDPPositiveUniversal

/-!
# André E1・E2：係数を保つ同型に沿う実 pd 包の源への移送

## 概要

主分冪表示との代数同型は、源の実分冪構造・入力元の分冪値・pd 普遍性を与える。
BS Rem 7.15(1)（著者版 p.62）の実テンソル側を pd 包として扱う準備。

## 方針

正次数イデアルを逆同型で写し、両方向が分冪射となることから普遍性を移す。

## 規約

係数作用を保つ代数同型と比較先の実分冪構造を明示する。ねじれや完備性は不要。

## 使われ方

根変数上で自然性を検証した実 Frobenius テンソルに分冪包の構造を戻す。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (y : A)
variable {B : Type v} [CommRing B] [Algebra A B]
variable (e : B ≃ₐ[A] PrincipalDPPresentation A y)

/-- 概要：実同型の源の分冪イデアルは正次数イデアルの逆像として指定する。
方針：逆環同型による像イデアルを使う。
規約：同じ源環のイデアルを構成する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 源のイデアル。 -/
def principalPDSourceIdeal : Ideal B :=
  (principalDPPositiveIdeal y).map e.symm.toRingHom

/-- 概要：同型の源にも比較先から実分冪構造を戻せる。
方針：逆環同型による分冪構造の移送を使う。
規約：比較先の分冪構造を明示する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実テンソル上の構造。 -/
def principalPDSourceDividedPowers (Hs : DividedPowers (principalDPPositiveIdeal y)) :
    DividedPowers (principalPDSourceIdeal y e) :=
  DividedPowers.ofRingEquiv rfl Hs

/-- 概要：源の分冪イデアルは元の入力元の係数像を含む。
方針：比較先での入力元の所属と逆代数同型の係数可換性を使う。
規約：同じ入力 y の像を扱う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の pd 包の入力条件。 -/
theorem principalPDSourceIdeal_base_mem : algebraMap A B y ∈ principalPDSourceIdeal y e := by
  rw [← e.symm.commutes y]
  exact Ideal.mem_map_of_mem e.symm.toRingHom (principalDPPositiveIdeal_base_mem y)

/-- 概要：源の分冪構造に対して順同型は分冪射。
方針：像イデアルの逆合成と移送された分冪の定義を使う。
規約：比較先の実分冪構造を保つ。
使われ方：BS Rem 7.15(1)（著者版 p.62）の pd 普遍性の移送。 -/
theorem principalPDSourceEquiv_isDPMorphism (Hs : DividedPowers (principalDPPositiveIdeal y)) :
    (principalPDSourceDividedPowers y e Hs).IsDPMorphism Hs e.toRingHom := by
  refine ⟨?_, ?_⟩
  · exact le_of_eq ((principalDPPositiveIdeal y).map_of_equiv e.symm.toRingEquiv)
  · intro n b hb
    change Hs.dpow n (e b) = e (e.symm (Hs.dpow n (e b)))
    exact (e.apply_symm_apply _).symm

/-- 概要：逆同型も比較先から源への分冪射。
方針：移送イデアルの定義と分冪作用の移送公式を使う。
規約：順逆の実構造を同じものに固定する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の普遍射の一意性。 -/
theorem principalPDSourceEquiv_symm_isDPMorphism
    (Hs : DividedPowers (principalDPPositiveIdeal y)) :
    Hs.IsDPMorphism (principalPDSourceDividedPowers y e Hs) e.symm.toRingHom := by
  refine ⟨le_rfl, ?_⟩
  intro n a ha
  exact DividedPowers.ofRingEquiv_dpow_apply rfl Hs

/-- 概要：源の入力元の標準分冪値は比較先の標準生成元の逆像。
方針：逆同型の分冪射性と係数可換性を使う。
規約：全次数 n の入力値を明示する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 生成元。 -/
theorem principalPDSourceDividedPowers_base_apply
    (Hs : DividedPowers (principalDPPositiveIdeal y))
    (hγ : ∀ n, Hs.dpow n (algebraMap A (PrincipalDPPresentation A y) y) =
      principalDPGenerator y n) (n : ℕ) :
    (principalPDSourceDividedPowers y e Hs).dpow n (algebraMap A B y) =
      e.symm (principalDPGenerator y n) := by
  rw [← e.symm.commutes y]
  change (principalPDSourceDividedPowers y e Hs).dpow n
    (e.symm.toRingHom (algebraMap A (PrincipalDPPresentation A y) y)) = _
  rw [(principalPDSourceEquiv_symm_isDPMorphism y e Hs).dpow_comp _
    (principalDPPositiveIdeal_base_mem y), hγ]
  rfl

/-- 概要：同じ実同型の源から任意の分冪標的への係数を保つ分冪射は一意に存在。
方針：比較先の普遍射を順同型と合成し、一意性は逆同型で戻して使う。
規約：標的の宇宙・ねじれ・完備性を制約しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実テンソルを pd 包とする普遍性。 -/
theorem existsUnique_principalPDSourceMorphism
    (Hs : DividedPowers (principalDPPositiveIdeal y))
    (hγ : ∀ n, Hs.dpow n (algebraMap A (PrincipalDPPresentation A y) y) =
      principalDPGenerator y n)
    {C : Type w} [CommRing C] [Algebra A C] {I : Ideal C}
    (Ht : DividedPowers I) (hyC : algebraMap A C y ∈ I) :
    ∃! F : B →ₐ[A] C,
      (principalPDSourceDividedPowers y e Hs).IsDPMorphism Ht F.toRingHom := by
  obtain ⟨F, hF, huniq⟩ := existsUnique_principalDPPositiveMorphism y Hs hγ Ht hyC
  refine ⟨F.comp e.toAlgHom, ?_, ?_⟩
  · exact DividedPowers.IsDPMorphism.comp Ht hF (principalPDSourceEquiv_isDPMorphism y e Hs)
  · intro G hG
    have hG' := DividedPowers.IsDPMorphism.comp Ht hG
      (principalPDSourceEquiv_symm_isDPMorphism y e Hs)
    have heq := huniq (G.comp e.symm.toAlgHom) hG'
    apply AlgHom.ext
    intro b
    simpa only [AlgHom.comp_apply, AlgEquiv.symm_apply_apply, AlgEquiv.coe_toAlgHom] using
      DFunLike.congr_fun heq (e b)

/-- 概要：係数を保つ主分冪表示への同型は通常多項式の評価も保つ。
方針：同型の単射性で比較先へ移し、評価と環射の可換性を使う。
規約：係数環作用と入力変数の像を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の自然な実テンソルで元の f を評価する。 -/
theorem principalPDSourcePolynomialEvaluation
    {K : Type w} [CommRing K] [Algebra K A] [Algebra K B]
    [Algebra K (PrincipalDPPresentation A y)]
    (x : A) (b : B)
    (hK : ∀ r : K, e (algebraMap K B r) = algebraMap K (PrincipalDPPresentation A y) r)
    (hA : ∀ r : K, algebraMap A (PrincipalDPPresentation A y) (algebraMap K A r) =
      algebraMap K (PrincipalDPPresentation A y) r)
    (hx : e b = algebraMap A (PrincipalDPPresentation A y) x) (g : Polynomial K) :
    algebraMap A B (g.eval₂ (algebraMap K A) x) = g.eval₂ (algebraMap K B) b := by
  have hc : e.toRingHom.comp (algebraMap K B) = algebraMap K (PrincipalDPPresentation A y) :=
    RingHom.ext hK
  have hca : (algebraMap A (PrincipalDPPresentation A y)).comp (algebraMap K A) =
      algebraMap K (PrincipalDPPresentation A y) := RingHom.ext hA
  have heval := Polynomial.hom_eval₂ g (algebraMap K B) e.toRingHom b
  rw [hc] at heval
  change e (g.eval₂ (algebraMap K B) b) =
    g.eval₂ (algebraMap K (PrincipalDPPresentation A y)) (e b) at heval
  rw [hx] at heval
  apply e.injective
  calc
    e (algebraMap A B (g.eval₂ (algebraMap K A) x)) =
        algebraMap A (PrincipalDPPresentation A y) (g.eval₂ (algebraMap K A) x) := e.commutes _
    _ = g.eval₂ (algebraMap K (PrincipalDPPresentation A y))
        (algebraMap A (PrincipalDPPresentation A y) x) := by
      rw [Polynomial.hom_eval₂, hca]
    _ = e (g.eval₂ (algebraMap K B) b) := heval.symm

end SerrePositivity.BhattScholze.Andre
