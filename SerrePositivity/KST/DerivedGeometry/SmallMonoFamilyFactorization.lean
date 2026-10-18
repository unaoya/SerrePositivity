module

public import SerrePositivity.KST.DerivedGeometry.SmallMonoFamilyArgument

/-!
概要：Grothendieck アーベル圏の小さい単射族に対する実際の単射・右持ち上げ因子分解。
方針：証明済みの small object argument と単射の左右持ち上げ判定を使う。
規約：準同型性や K-injectivity をこの一般の単射族については主張しない。
使われ方：Stacks 19.12.3・19.12.6、TT §3・§8、Toën §3.2 の非有界分解の接続点。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v u
open CategoryTheory Limits MorphismProperty
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {σ : Type w} {A B : σ → C} (i : ∀ s, A s ⟶ B s) [∀ s, Mono (i s)]

/--
概要：小さい単射族から生成される左持ち上げ射は単射。
方針：元の族と単射全体の包含を二回の反変な持ち上げ操作で移す。
規約：Grothendieck 圏の単射の左右持ち上げ判定を使う。
使われ方：Stacks 19.12.6、TT §3 の単射な超限因子分解。
-/
lemma smallMonoFamily_llp_rlp_le_monomorphisms : (ofHoms i).rlp.llp ≤ monomorphisms C := by
  rw [← IsGrothendieckAbelian.llp_rlp_monomorphisms (isSeparator_separator C)]
  exact antitone_llp (antitone_rlp (smallMonoFamily_le_monomorphisms i))

/--
概要：任意の射は単射と指定した小さい単射族に対する右持ち上げ射に因子分解できる。
方針：実際の small object factorization の左射の単射性を証明する。
規約：因子分解の存在をフィールドとして仮定しない。
使われ方：Stacks 19.12.6、TT §3・§8、Toën §3.2 の非有界分解の因子分解。
-/
lemma smallMonoFamily_exists_factorization {X Y : C} (f : X ⟶ Y) :
    ∃ (Z : C) (l : X ⟶ Z) (r : Z ⟶ Y), l ≫ r = f ∧ Mono l ∧ (ofHoms i).rlp r := by
  have : HasSmallObjectArgument.{w} (ofHoms i) := smallMonoFamily_hasSmallObjectArgument i
  let d := factorizationData (ofHoms i).rlp.llp (ofHoms i).rlp f
  exact ⟨d.Z, d.i, d.p, d.fac, smallMonoFamily_llp_rlp_le_monomorphisms i _ d.hi, d.hp⟩

end SerrePositivity.KST.DerivedGeometry
