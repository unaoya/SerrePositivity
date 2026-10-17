module
public import SerrePositivity.DifferentialGraded.Tensor.SphereFreeKFlat

/-! # 全cycleを生成元とするK-flat複体被覆

## 概要
増大射はcycle上全射であり、各次数のホモロジーでも全射となる。
単射性は主張しない。dg圏の初期増大に使う。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex MonoidalCategory
variable (A : Type u) [CommRing A]

lemma complexSphereCycle_comp {K L : Complex A} (n : ℤ)
    (f : complexSphere A n ⟶ K) (g : K ⟶ L) :
    (complexSphereCycle A n (f ≫ g)).val =
      g.f n (complexSphereCycle A n f).val := rfl

/-- 任意整数次数の全cycleを添字とする。 -/
abbrev ComplexCycleIndex (K : Complex A) := Σ n : ℤ, complexCycles A K n

abbrev complexCycleCover (K : Complex A) : Complex A :=
  ∐ (fun j : ComplexCycleIndex A K => complexSphere A j.1)

def complexCycleCoverπ (K : Complex A) : complexCycleCover A K ⟶ K :=
  Sigma.desc (fun j => complexSphereMap A j.1 j.2)

lemma complexCycleCoverι_π (K : Complex A) (j : ComplexCycleIndex A K) :
    Sigma.ι (fun i : ComplexCycleIndex A K => complexSphere A i.1) j ≫
      complexCycleCoverπ A K = complexSphereMap A j.1 j.2 := Sigma.ι_comp_desc _ _

lemma complexCycleCover_kFlat (K : Complex A) : complexKFlat A (complexCycleCover A K) := by
  have : HasExactColimitsOfShape (Discrete (ComplexCycleIndex A K)) (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (Discrete.equivalence (equivShrink.{u} (ComplexCycleIndex A K)).symm)
  exact complexKFlat_colimit A
    (Discrete.functor fun j : ComplexCycleIndex A K => complexSphere A j.1)
    (fun j => complexSphere_kFlat A j.as.1)

/-- 指定cycleのsphere射を初期被覆へ持ち上げる。 -/
def complexCycleCoverLift (K : Complex A) (n : ℤ) (z : complexCycles A K n) :
    complexSphere A n ⟶ complexCycleCover A K :=
  Sigma.ι (fun j : ComplexCycleIndex A K => complexSphere A j.1) ⟨n, z⟩

lemma complexCycleCoverLift_π (K : Complex A) (n : ℤ) (z : complexCycles A K n) :
    complexCycleCoverLift A K n z ≫ complexCycleCoverπ A K = complexSphereMap A n z :=
  complexCycleCoverι_π A K ⟨n, z⟩

lemma complexCycleCover_cycle_lift (K : Complex A) (n : ℤ) (z : complexCycles A K n) :
    ∃ t : complexCycles A (complexCycleCover A K) n,
      (complexCycleCoverπ A K).f n t.val = z.val := by
  refine ⟨complexSphereCycle A n (complexCycleCoverLift A K n z), ?_⟩
  rw [← complexSphereCycle_comp, complexCycleCoverLift_π]
  exact congrArg Subtype.val ((complexSphereHomEquiv A K n).apply_symm_apply z)

/-- cycleの厳密な持ち上げからMathlibのcyclesMapの全射性を得る。 -/
lemma complexCyclesMap_epi_of_cycle_lift {K L : Complex A} (f : K ⟶ L) (n : ℤ)
    (h : ∀ z : complexCycles A L n, ∃ t : complexCycles A K n, f.f n t.val = z.val) :
    Epi (cyclesMap f n) := by
  apply (ModuleCat.epi_iff_surjective _).2
  intro z
  have hz : L.d n (n + 1) (L.iCycles n z) = 0 := by
    exact congrArg (fun k => k z) (L.iCycles_d n (n + 1))
  obtain ⟨t, ht⟩ := h ⟨L.iCycles n z, hz⟩
  let k := moduleElementMap A (K.X n) t.val
  have hk : k ≫ K.d n (n + 1) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change K.d n (n + 1) (a • t.val) = 0
    rw [map_smul, t.property, smul_zero]
  let q := K.liftCycles k (n + 1) (by simp) hk
  refine ⟨q (1 : A), ?_⟩
  apply (ModuleCat.mono_iff_injective (L.iCycles n)).1 inferInstance
  have hc := congrArg (fun k => k (1 : A))
    (show q ≫ cyclesMap f n ≫ L.iCycles n = k ≫ f.f n by
      rw [cyclesMap_i, ← Category.assoc, liftCycles_i])
  change L.iCycles n (cyclesMap f n (q (1 : A))) = f.f n ((1 : A) • t.val) at hc
  simpa only [one_smul] using hc.trans (by simpa only [one_smul] using ht)

lemma complexHomologyMap_epi_of_cycle_lift {K L : Complex A} (f : K ⟶ L) (n : ℤ)
    (h : ∀ z : complexCycles A L n, ∃ t : complexCycles A K n, f.f n t.val = z.val) :
    Epi (homologyMap f n) := by
  have := complexCyclesMap_epi_of_cycle_lift A f n h
  exact ShortComplex.epi_homologyMap_of_epi_cyclesMap'
    ((shortComplexFunctor (ModuleCat A) (.up ℤ) n).map f) this

lemma complexCycleCover_homology_epi (K : Complex A) (n : ℤ) :
    Epi (homologyMap (complexCycleCoverπ A K) n) :=
  complexHomologyMap_epi_of_cycle_lift A _ n (complexCycleCover_cycle_lift A K n)

end SerrePositivity.DifferentialGraded
