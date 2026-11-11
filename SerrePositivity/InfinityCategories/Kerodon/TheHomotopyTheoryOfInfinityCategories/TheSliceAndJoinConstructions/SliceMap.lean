module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Coslice

/-!
概要：slice と coslice の図式の制限および標的への射の作用。
方針：join からの射の前合成と後合成で次数ごとに定義する。
規約：slice の図式変数には反変、標的変数には共変。
使われ方：HTT §2.1.2・4.1.1、Kerodon §4.3.6（Tag 018E） の相対的な持ち上げ問題。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：図式の前合成が coslice に誘導する制限射。
方針：各錐を左因子の射で前合成する。
規約：f:K₀→K に対し X_{p/}→X_{pf/}。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6（Tag 018E） の相対 coslice。 -/
def sliceUnderRestrict {K₀ K X : SSet.{u}} (p : K ⟶ X) (f : K₀ ⟶ K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (f ≫ p) where
  app n := ↾fun σ ↦ ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 (stdSimplex.obj n.unop)) ≫ σ.val, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, σ.property]⟩
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 _) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.map α.unop) ≫ σ.val) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K₀) (stdSimplex.map α.unop) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 _) ≫ σ.val)
    simp only [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, Category.comp_id]

/-- 概要：標的への射が coslice に誘導する射。
方針：各錐を標的の射で後合成する。
規約：q:X→Y に対し X_{p/}→Y_{qp/}。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6（Tag 018E） の相対 coslice。 -/
def sliceUnderPostcomp {K X Y : SSet.{u}} (p : K ⟶ X) (q : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (p ≫ q) where
  app _ := ↾fun σ ↦ ⟨σ.val ≫ q, by rw [← Category.assoc, σ.property]⟩
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    exact Category.assoc _ _ _

/-- 概要：図式の前合成が slice に誘導する制限射。
方針：各錐を右因子の射で前合成する。
規約：f:K₀→K に対し X_{/p}→X_{/pf}。
使われ方：HTT §2.1.2・4.1.1、Kerodon Corollary 4.3.6.14（Tag 018L） の制限射。 -/
def sliceOverRestrict {K₀ K X : SSet.{u}} (p : K ⟶ X) (f : K₀ ⟶ K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (f ≫ p) where
  app n := ↾fun σ ↦ ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (stdSimplex.obj n.unop)) f ≫ σ.val, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc, σ.property]⟩
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map α.unop) (𝟙 K) ≫ σ.val) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map α.unop) (𝟙 K₀) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) f ≫ σ.val)
    simp only [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, Category.comp_id]

/-- 概要：標的への射が slice に誘導する射。
方針：各錐を標的の射で後合成する。
規約：q:X→Y に対し X_{/p}→Y_{/qp}。
使われ方：HTT §2.1.2、Kerodon §4.3.6（Tag 018E） の相対 slice。 -/
def sliceOverPostcomp {K X Y : SSet.{u}} (p : K ⟶ X) (q : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (p ≫ q) where
  app _ := ↾fun σ ↦ ⟨σ.val ≫ q, by rw [← Category.assoc, σ.property]⟩
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    exact Category.assoc _ _ _

/-- 概要：coslice の制限と標的への射の作用は可換。
方針：各次数の錐の前後合成の結合律を使う。
規約：合成した図式の括弧は NatTrans の結合律による等式で一致する。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6（Tag 018E） の相対 coslice の射。 -/
lemma sliceUnderRestrict_postcomp {K₀ K X Y : SSet.{u}} (p : K ⟶ X)
    (f : K₀ ⟶ K) (q : X ⟶ Y) :
    sliceUnderPostcomp p q ≫ sliceUnderRestrict (p ≫ q) f =
      sliceUnderRestrict p f ≫ sliceUnderPostcomp (f ≫ p) q := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  apply Subtype.ext
  exact (Category.assoc _ _ _).symm

/-- 概要：slice の制限と標的への射の作用は可換。
方針：各次数の錐の前後合成の結合律を使う。
規約：図式の合成は Mathlib の順序。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6（Tag 018E） の相対 slice の射。 -/
lemma sliceOverRestrict_postcomp {K₀ K X Y : SSet.{u}} (p : K ⟶ X)
    (f : K₀ ⟶ K) (q : X ⟶ Y) :
    sliceOverPostcomp p q ≫ sliceOverRestrict (p ≫ q) f =
      sliceOverRestrict p f ≫ sliceOverPostcomp (f ≫ p) q := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  apply Subtype.ext
  exact (Category.assoc _ _ _).symm

/-- 概要：coslice の普遍性の curry は束ねた射を元の射へ戻す。
方針：直接構成した同値の左逆関係を使う。
規約：固定条件は uncurry の固定条件を使う。
使われ方：HTT §2.1.2、Kerodon §4.3.6（Tag 018E） の持ち上げの移送。 -/
lemma sliceUnderCurry_uncurry {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed f) = f :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderEquiv p).symm_apply_apply f

/-- 概要：coslice の普遍性の uncurry は curry した射を元の join からの射へ戻す。
方針：直接構成した同値の右逆関係を使う。
規約：hF は左因子上の固定条件。
使われ方：HTT §2.1.2、Kerodon §4.3.6（Tag 018E） の持ち上げの移送。 -/
lemma sliceUnderUncurry_curry {A K X : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K A ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A ≫ F = p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry F hF) = F :=
  congrArg Subtype.val ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderEquiv p).apply_symm_apply ⟨F, hF⟩)

/-- 概要：coslice の curry は右の変数での前合成と可換。
方針：Yoneda の自然性と joinMap の合成則を使う。
規約：g は錐の頂点側の単体集合の射。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6（Tag 018E） の持ち上げ正方形。 -/
lemma sliceUnderCurry_precomp {A₀ A K X : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K A ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A ≫ F = p) (g : A₀ ⟶ A) :
    g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry F hF =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) g ≫ F)
        (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp, hF]) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (SSet.yonedaEquiv.symm (g.app n a)) ≫ F =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (SSet.yonedaEquiv.symm a) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) g ≫ F)
  rw [← SSet.yonedaEquiv_symm_comp]
  simp only [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]

/-- 概要：coslice の curry は図式の制限と可換。
方針：独立な左右因子の joinMap の可換性を使う。
規約：f は固定された図式側の射。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6（Tag 018E） の持ち上げ正方形。 -/
lemma sliceUnderCurry_restrict {A K₀ K X : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K A ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A ≫ F = p) (f : K₀ ⟶ K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry F hF ≫ sliceUnderRestrict p f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 A) ≫ F)
        (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, hF]) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 _) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (SSet.yonedaEquiv.symm a) ≫ F) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K₀) (SSet.yonedaEquiv.symm a) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 A) ≫ F)
  simp only [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, Category.comp_id]

/-- 概要：coslice の curry は標的への射との後合成と可換。
方針：各錐の合成の結合律を使う。
規約：q は標的の単体集合の射。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6（Tag 018E） の持ち上げ正方形。 -/
lemma sliceUnderCurry_postcomp {A K X Y : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K A ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A ≫ F = p) (q : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry F hF ≫ sliceUnderPostcomp p q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry (F ≫ q) (by rw [← Category.assoc, hF]) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  exact Category.assoc _ _ _

/-- 概要：coslice への射の uncurry は前合成と可換。
方針：curry と uncurry の逆関係を前合成の式に適用する。
規約：g は自由な変数側の射。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6（Tag 018E） の持ち上げ正方形。 -/
lemma sliceUnderUncurry_precomp {A₀ A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) (g : A₀ ⟶ A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (g ≫ f) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry f := by
  have h := sliceUnderCurry_precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed f) g
  rw [sliceUnderCurry_uncurry] at h
  rw [h, sliceUnderUncurry_curry]

/-- 概要：coslice への射の uncurry は図式の制限と可換。
方針：curry と uncurry の逆関係を制限の式に適用する。
規約：g は固定された図式側の射。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6（Tag 018E） の持ち上げ正方形。 -/
lemma sliceUnderUncurry_restrict {A K₀ K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) (g : K₀ ⟶ K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (f ≫ sliceUnderRestrict p g) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap g (𝟙 A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry f := by
  have h := sliceUnderCurry_restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed f) g
  rw [sliceUnderCurry_uncurry] at h
  rw [h, sliceUnderUncurry_curry]

/-- 概要：coslice への射の uncurry は標的の後合成と可換。
方針：curry と uncurry の逆関係を後合成の式に適用する。
規約：q は標的の射。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6（Tag 018E） の持ち上げ正方形。 -/
lemma sliceUnderUncurry_postcomp {A K X Y : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) (q : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (f ≫ sliceUnderPostcomp p q) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry f ≫ q := by
  have h := sliceUnderCurry_postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed f) q
  rw [sliceUnderCurry_uncurry] at h
  rw [h, sliceUnderUncurry_curry]

/-- 概要：slice の普遍性の curry は束ねた射を元の射へ戻す。
方針：直接構成した同値の左逆関係を使う。
規約：固定条件は uncurry の固定条件を使う。
使われ方：HTT §2.1.2、Kerodon §4.3.6（Tag 018E） の持ち上げの移送。 -/
lemma sliceOverCurry_uncurry {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed f) = f :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverEquiv p).symm_apply_apply f

/-- 概要：slice の普遍性の uncurry は curry した射を元の join からの射へ戻す。
方針：直接構成した同値の右逆関係を使う。
規約：hF は右因子上の固定条件。
使われ方：HTT §2.1.2、Kerodon §4.3.6（Tag 018E） の持ち上げの移送。 -/
lemma sliceOverUncurry_curry {A K X : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K ≫ F = p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry F hF) = F :=
  congrArg Subtype.val ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverEquiv p).apply_symm_apply ⟨F, hF⟩)

/-- 概要：slice の curry は左の変数での前合成と可換。
方針：Yoneda の自然性と joinMap の合成則を使う。
規約：g は錐の頂点側の単体集合の射。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6（Tag 018E） の持ち上げ正方形。 -/
lemma sliceOverCurry_precomp {A₀ A K X : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K ≫ F = p) (g : A₀ ⟶ A) :
    g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry F hF =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap g (𝟙 K) ≫ F)
        (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp, hF]) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm (g.app n a)) (𝟙 K) ≫ F =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a) (𝟙 K) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap g (𝟙 K) ≫ F)
  rw [← SSet.yonedaEquiv_symm_comp]
  simp only [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]

/-- 概要：slice の curry は図式の制限と可換。
方針：独立な左右因子の joinMap の可換性を使う。
規約：f は固定された図式側の射。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6（Tag 018E） の持ち上げ正方形。 -/
lemma sliceOverCurry_restrict {A K₀ K X : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K ≫ F = p) (f : K₀ ⟶ K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry F hF ≫ sliceOverRestrict p f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) f ≫ F)
        (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc, hF]) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a) (𝟙 K) ≫ F) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a) (𝟙 K₀) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) f ≫ F)
  simp only [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, Category.comp_id]

/-- 概要：slice の curry は標的への射との後合成と可換。
方針：各錐の合成の結合律を使う。
規約：q は標的の単体集合の射。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6（Tag 018E） の持ち上げ正方形。 -/
lemma sliceOverCurry_postcomp {A K X Y : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K ≫ F = p) (q : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry F hF ≫ sliceOverPostcomp p q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry (F ≫ q) (by rw [← Category.assoc, hF]) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  exact Category.assoc _ _ _

/-- 概要：slice への射の uncurry は前合成と可換。
方針：curry と uncurry の逆関係を前合成の式に適用する。
規約：g は自由な変数側の射。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6（Tag 018E） の持ち上げ正方形。 -/
lemma sliceOverUncurry_precomp {A₀ A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) (g : A₀ ⟶ A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (g ≫ f) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap g (𝟙 K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry f := by
  have h := sliceOverCurry_precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed f) g
  rw [sliceOverCurry_uncurry] at h
  rw [h, sliceOverUncurry_curry]

/-- 概要：slice への射の uncurry は図式の制限と可換。
方針：curry と uncurry の逆関係を制限の式に適用する。
規約：g は固定された図式側の射。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6（Tag 018E） の持ち上げ正方形。 -/
lemma sliceOverUncurry_restrict {A K₀ K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) (g : K₀ ⟶ K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (f ≫ sliceOverRestrict p g) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry f := by
  have h := sliceOverCurry_restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed f) g
  rw [sliceOverCurry_uncurry] at h
  rw [h, sliceOverUncurry_curry]

/-- 概要：slice への射の uncurry は標的の後合成と可換。
方針：curry と uncurry の逆関係を後合成の式に適用する。
規約：q は標的の射。
使われ方：HTT Lemma 2.1.2.3、Kerodon §4.3.6（Tag 018E） の持ち上げ正方形。 -/
lemma sliceOverUncurry_postcomp {A K X Y : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) (q : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (f ≫ sliceOverPostcomp p q) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry f ≫ q := by
  have h := sliceOverCurry_postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed f) q
  rw [sliceOverCurry_uncurry] at h
  rw [h, sliceOverUncurry_curry]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
