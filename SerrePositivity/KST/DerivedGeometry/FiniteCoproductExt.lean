module

public import SerrePositivity.KST.DerivedGeometry.ResolutionExtCriterion
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
概要：有限余積を始域とする Ext の消滅判定。
方針：有限余積と双積の標準同型と実際の Ext の双積比較を使う。
規約：次数や標的の injectivity に条件を加えない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の有限 Čech 分解の各項。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
open CategoryTheory Limits Abelian
namespace SerrePositivity.KST.DerivedGeometry
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/--
概要：各因子からの Ext が消えると有限余積からの Ext も消える。
方針：双積との同型で始域を移し、Ext の双積の加法的同値で成分ごとに判定する。
規約：有限余積と Hom の一致を未証明のフィールドとして要求しない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の Čech 次元移動。
-/
lemma finiteCoproduct_ext_subsingleton {ι : Type t} [Finite ι]
    (Z : ι → A) [HasBiproduct Z] (F : A) (n : ℕ)
    (h : ∀ i, Subsingleton (Ext (Z i) F n)) : Subsingleton (Ext (∐ Z) F n) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let e := ((evaluation A AddCommGrpCat.{w}).obj F).mapIso
    ((extFunctor n).mapIso (biproduct.isoCoproduct Z).op)
  have (i : ι) : Subsingleton (Ext (Z i) F n) := h i
  constructor
  intro α β
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  apply (Ext.biproductAddEquiv (biproduct.isBilimit Z) F n).injective
  exact Subsingleton.elim _ _

/--
概要：始域の同型に沿って Ext の消滅を移す。
方針：Ext の実際の反変関手で同型を移し、その逆の単射性を使う。
規約：任意の次数の Ext について述べる。
使われ方：TT §3、Toën §3.2 の選ばれた余積との比較。
-/
lemma ext_subsingleton_of_iso {X Y : A} (e : X ≅ Y) (F : A) (n : ℕ)
    (h : Subsingleton (Ext Y F n)) : Subsingleton (Ext X F n) := by
  let i := ((evaluation A AddCommGrpCat.{w}).obj F).mapIso ((extFunctor n).mapIso e.op)
  constructor
  intro α β
  apply (ConcreteCategory.bijective_of_isIso i.inv).injective
  exact h.elim _ _

/--
概要：有限余積を始域とする Ext の類は各挿入への制限で零を検出できる。
方針：双積との比較を介し Ext の成分同値の単射性を使う。
規約：各成分の Ext 自体の消滅は仮定しない。
使われ方：TT §3・§8、Toën §3.2 の被覆上で消える類の検出。
-/
lemma finiteCoproduct_ext_eq_zero {ι : Type t} [Finite ι]
    (Z : ι → A) [HasBiproduct Z] (F : A) (n : ℕ) (α : Ext (∐ Z) F n)
    (h : ∀ i, (Ext.mk₀ (Sigma.ι Z i)).comp α (zero_add n) = 0) : α = 0 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let e := ((evaluation A AddCommGrpCat.{w}).obj F).mapIso
    ((extFunctor n).mapIso (biproduct.isoCoproduct Z).op)
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  apply (Ext.biproductAddEquiv (biproduct.isBilimit Z) F n).injective
  simp only [map_zero]
  ext i
  change (Ext.mk₀ (biproduct.ι Z i)).comp
    ((Ext.mk₀ (biproduct.isoCoproduct Z).hom).comp α (zero_add n)) (zero_add n) = 0
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  simpa using h i

end SerrePositivity.KST.DerivedGeometry
