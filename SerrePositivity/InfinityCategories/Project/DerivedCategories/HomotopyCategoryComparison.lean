module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.InfinityCategory
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DerivedComparisonShift
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomotopyCategory

/-! # 導来 ∞ 圏のホモトピー圏と通常の導来圏

概要：semifree dg nerve のホモトピー圏を Mathlib の導来圏と同一視する。
方針：N3 の H⁰ 比較と D2 の導来同値を合成し、整数シフトも H⁰ を通して移す。
規約：ホモトピー圏は二次切断によるもの。使われ方：導来 ∞ 圏と古典的導来圏の橋。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S]

/-- 概要：導来 ∞ 圏の二次切断によるホモトピー圏。
方針：N3 の dg nerve のホモトピー圏を具体化する。
規約：対象は semifree 複体。使われ方：通常の導来圏との比較の始域。 -/
abbrev derivedInfinityHomotopyCategory :=
  SSet.Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S))

/-- 概要：導来 ∞ 圏のホモトピー圏は semifree dg 圏の H⁰ と同値である。
方針：N3 の無条件の同値を具体化する。
規約：辺の類を閉零射の境界類へ送る。使われ方：D2 との合成。 -/
def derivedInfinityH0Equivalence : derivedInfinityHomotopyCategory S ≌
    DifferentialGraded.HomotopyCategory S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equivalence S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)

/-- 概要：導来 ∞ 圏のホモトピー圏の整数シフト関手。
方針：H⁰ のシフトを N3 の同値を介して移す。
規約：整数シフトの符号は D2f を継承する。使われ方：同値のシフト整合性。 -/
def derivedInfinityHomotopyShift (s : ℤ) :
    derivedInfinityHomotopyCategory S ⥤ derivedInfinityHomotopyCategory S :=
  ((derivedInfinityH0Equivalence S).functor ⋙
    shiftFunctor (DifferentialGraded.HomotopyCategory S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)) s) ⋙
      (derivedInfinityH0Equivalence S).inverse

/-- 概要：移したシフトと H⁰ 比較の間の自然同型。
方針：H⁰ 同値の余単位で往復を消去する。
規約：全整数シフトに一様。使われ方：零・加法の整合性の誘導。 -/
def derivedInfinityHomotopyShiftIso (s : ℤ) :
    derivedInfinityHomotopyShift S s ⋙ (derivedInfinityH0Equivalence S).functor ≅
      (derivedInfinityH0Equivalence S).functor ⋙ shiftFunctor _ s :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (derivedInfinityH0Equivalence S).counitIso ≪≫ Functor.rightUnitor _

/-- 概要：導来 ∞ 圏のホモトピー圏は整合的な整数シフトを持つ。
方針：充満忠実な H⁰ 比較を通じてシフトの coherence を誘導する。
規約：D2f のシフトを移す。使われ方：導来比較の CommShift。 -/
instance derivedInfinityHomotopyHasShift : HasShift (derivedInfinityHomotopyCategory S) ℤ :=
  (Functor.FullyFaithful.ofFullyFaithful (derivedInfinityH0Equivalence S).functor).hasShift
    (derivedInfinityHomotopyShift S) (derivedInfinityHomotopyShiftIso S)

/-- 概要：N3 の H⁰ 比較は整数シフトと両立する。
方針：充満忠実関手を通じた誘導シフトの標準比較を使う。
規約：零と加法の coherence を含む。使われ方：D2f の整合性との合成。 -/
instance derivedInfinityH0EquivalenceCommShift :
    (derivedInfinityH0Equivalence S).functor.CommShift ℤ :=
  Functor.CommShift.ofHasShiftOfFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful (derivedInfinityH0Equivalence S).functor)
    (derivedInfinityHomotopyShift S) (derivedInfinityHomotopyShiftIso S)

variable [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 概要：D(S) のホモトピー圏は Mathlib の導来圏と圏同値である。
方針：N3 の H⁰ 比較と semifree 導来同値を合成する。
規約：有界性や環の追加性質は仮定しない。使われ方：導来 ∞ 圏の古典的な同定。 -/
def derivedInfinityHomotopyEquivalence :
    derivedInfinityHomotopyCategory S ≌ DerivedCategory (ModuleCat.{u} S) :=
  (derivedInfinityH0Equivalence S).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeDerivedEquivalence S)

/-- 概要：D(S) のホモトピー圏から導来圏への同値は整数シフトと両立する。
方針：N3 を通した比較と D2f の CommShift を合成する。
規約：零と加法の coherence も保存する。使われ方：三角構造の比較。 -/
instance derivedInfinityHomotopyEquivalenceCommShift :
    (derivedInfinityHomotopyEquivalence S).functor.CommShift ℤ := by
  change ((derivedInfinityH0Equivalence S).functor ⋙
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeDerivedEquivalence S).functor).CommShift ℤ
  infer_instance

/-- 概要：導来同値の整数シフト比較を自然同型として取り出す。
方針：合成済みの CommShift の比較自然同型を用いる。
規約：任意の整数シフト。使われ方：シフトされた射と対象の比較。 -/
def derivedInfinityHomotopyEquivalenceShiftIso (s : ℤ) :
    shiftFunctor (derivedInfinityHomotopyCategory S) s ⋙
      (derivedInfinityHomotopyEquivalence S).functor ≅
        (derivedInfinityHomotopyEquivalence S).functor ⋙
          shiftFunctor (DerivedCategory (ModuleCat.{u} S)) s :=
  (derivedInfinityHomotopyEquivalence S).functor.commShiftIso s

end SerrePositivity.InfinityCategories.Project.DerivedCategories
