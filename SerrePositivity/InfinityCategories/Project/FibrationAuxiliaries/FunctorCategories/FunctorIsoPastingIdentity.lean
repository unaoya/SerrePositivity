module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoPastingTransport

/-!
概要：端点の表示を含めた、指定関手同型の二因子の貼り合わせ等式。
方針：同じ指定値の貼り合わせを命題に包み、終辺の同じ値への移送を保存する。
規約：等式の内容と元の同型の指定値を保持する。
使われ方：大きな大域 Hom 上の三角等式を一般の貼り合わせ則から検証する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 二因子の指定合成は、端点の表示を除いて指定された終辺と同じ値。 -/
def FunctorIsoPastingHEq {X Y : SSet.{u}} {a b c a' c' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b c) (n : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a' c') : Prop :=
  HEq (e ≪≫ d) n

/-- 元の貼り合わせ等式の終辺を、その同じ指定値で置き換えられる。 -/
lemma functorIsoPastingHEq_of_eq_of_heq {X Y : SSet.{u}} {a b c a' c' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b c) (m : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a c)
    (n : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a' c') (h : e ≪≫ d = m) (hn : HEq n m) :
    FunctorIsoPastingHEq e d n := by
  exact HEq.trans (heq_of_eq h) hn.symm

/-- 三端点を同じ表示に正規化すると、指定された貼り合わせは通常の等式になる。 -/
lemma FunctorIsoPastingHEq.normalized {X Y : SSet.{u}} {a b c a' b' c' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b c) (n : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a' c')
    (ha : a = a') (hb : b = b') (hc : c = c') (h : FunctorIsoPastingHEq e d n) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e ha hb ≪≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq d hb hc = n := by
  subst a' b' c'
  exact eq_of_heq h

/-- 指定された第二因子を、正規化した第一因子の逆と終辺の合成に分解する等式。 -/
def FunctorIsoPastingRightFactorIdentity {X Y : SSet.{u}} {a b c a' b' c' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b c) (n : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a' c')
    (ha : a = a') (hb : b = b') (hc : c = c') : Prop :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq d hb hc = (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e ha hb).symm ≪≫ n

/-- 同じ端点へ正規化した第二因子は、指定された第一因子の逆と終辺の合成。 -/
lemma FunctorIsoPastingHEq.rightFactor {X Y : SSet.{u}} {a b c a' b' c' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b c) (n : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a' c')
    (ha : a = a') (hb : b = b') (hc : c = c') (h : FunctorIsoPastingHEq e d n) :
    FunctorIsoPastingRightFactorIdentity e d n ha hb hc := by
  unfold FunctorIsoPastingRightFactorIdentity
  have hh := FunctorIsoPastingHEq.normalized e d n ha hb hc h
  rw [← hh]
  simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

/-- 始点だけを同じ表示へ移した、指定された貼り合わせの等式。 -/
def FunctorIsoPastingSourceIdentity {X Y : SSet.{u}} {a b c a' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b c) (n : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a' c)
    (ha : a = a') : Prop := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e ha rfl ≪≫ d = n

/-- 始点だけの正規化では、同じ第二因子をそのまま保持できる。 -/
lemma FunctorIsoPastingHEq.normalizeSource {X Y : SSet.{u}} {a b c a' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b c) (n : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a' c)
    (ha : a = a') (h : FunctorIsoPastingHEq e d n) :
    FunctorIsoPastingSourceIdentity e d n ha := by
  subst a'
  exact eq_of_heq h

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
