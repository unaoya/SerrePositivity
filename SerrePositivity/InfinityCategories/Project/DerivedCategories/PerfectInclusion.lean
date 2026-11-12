module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectBasic

/-! # Perf の正本の包含と計算モデルの比較

概要：正本の Perf の包含は dg nerve モデルの包含と標準同型の下で一致する。
方針：像への分解と部分複体の等式の移送を計算する。
規約：単体集合の射の等式で比較する。使われ方：正本への引き戻し判定の転送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory
variable (S : Type u) [CommRing S]

/-- 概要：正本の Perf(S) から D(S) への包含。
方針：充満部分単体集合の標準包含を取る。
規約：部分型の値を返す。使われ方：D4 の比較射の入力。 -/
abbrev perfectInfinityInclusion : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityCategory S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinitySubcomplex S).ι

private lemma subcomplex_eq_ι {X : SSet.{u}} (K L : X.Subcomplex) (h : K = L) :
    eqToHom (congrArg (fun M : X.Subcomplex => (M : SSet.{u})) h) ≫ L.ι = K.ι := by
  cases h
  exact Category.id_comp _

/-- 概要：計算モデルから正本を経由する包含は元の dg nerve 包含である。
方針：像への分解と等しい部分複体の包含の式を使う。
規約：実際の射の等式。使われ方：正本とモデルの包含の整合。 -/
lemma perfectNerveModelIso_hom_inclusion :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveModelIso S).hom ≫ perfectInfinityInclusion S = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion S := by
  change (SSet.Subcomplex.toRange (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion S) ≫
    eqToHom (congrArg (fun K : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S).Subcomplex => (K : SSet.{u + 1}))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion_range S))) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinitySubcomplex S).ι = _
  rw [Category.assoc, subcomplex_eq_ι _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion_range S),
    SSet.Subcomplex.toRange_ι]

/-- 概要：正本から計算モデルを経由する包含は標準包含である。
方針：同型の順方向を前合成して逆則を消去する。
規約：モデルを経由した図式は周囲で同じ図式。使われ方：D4 の比較射の正本。 -/
lemma perfectNerveModelIso_inv_inclusion :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveModelIso S).inv ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion S = perfectInfinityInclusion S := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveModelIso S).hom).1
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, perfectNerveModelIso_hom_inclusion]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
