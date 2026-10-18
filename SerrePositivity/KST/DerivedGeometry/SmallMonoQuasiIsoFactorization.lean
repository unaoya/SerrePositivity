module

public import SerrePositivity.KST.DerivedGeometry.SmallMonoFamilyFactorization
public import SerrePositivity.KST.DerivedGeometry.MonoQuasiIsoCellClosure
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
概要：小さい単射準同型族の small object factorization の左射は単射準同型。
方針：cell の coproduct・押し出し・超限合成・retract の各工程での保存を適用する。
規約：左射の準同型性をフィールドとして仮定しない。
使われ方：Stacks 19.12.4・19.12.6、TT §3・§8、Toën §3.2 の非有界分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits MorphismProperty
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {σ : Type w} {A B : σ → CochainComplex C ℤ}
  (i : ∀ s, A s ⟶ B s) [∀ s, Mono (i s)]

/--
概要：小さい単射準同型族から生成される左持ち上げ射は単射準同型。
方針：small object argument の cell による記述と各工程での保存を使う。
規約：元の複体の圏の準同型性。
使われ方：Stacks 19.12.6、TT §3 の超限射の準同型性。
-/
lemma smallMonoQuasiIsoFamily_llp_rlp_le (h : ∀ s, QuasiIso (i s)) :
    (ofHoms i).rlp.llp ≤ monicQuasiIsomorphisms (C := C) := by
  have : HasSmallObjectArgument.{w} (ofHoms i) := smallMonoFamily_hasSmallObjectArgument i
  rw [llp_rlp_of_hasSmallObjectArgument]
  simp only [retracts_le_iff, transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
  rintro _ _ _ ⟨s⟩
  exact ⟨inferInstance, h s⟩

/--
概要：任意の射は単射準同型と指定した族への右持ち上げ射へ因子分解できる。
方針：実際の small object factorization の左射を保存定理で判定する。
規約：族の成分の準同型性だけを入力する。
使われ方：Stacks 19.12.6、TT §3・§8、Toën §3.2 の非有界 injective 模型。
-/
lemma smallMonoQuasiIsoFamily_exists_factorization (h : ∀ s, QuasiIso (i s))
    {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    ∃ (Z : CochainComplex C ℤ) (l : X ⟶ Z) (r : Z ⟶ Y),
      l ≫ r = f ∧ Mono l ∧ QuasiIso l ∧ (ofHoms i).rlp r := by
  have : HasSmallObjectArgument.{w} (ofHoms i) := smallMonoFamily_hasSmallObjectArgument i
  let d := factorizationData (ofHoms i).rlp.llp (ofHoms i).rlp f
  have hd := smallMonoQuasiIsoFamily_llp_rlp_le i h _ d.hi
  exact ⟨d.Z, d.i, d.p, d.fac, hd.1, hd.2, d.hp⟩

end SerrePositivity.KST.DerivedGeometry
