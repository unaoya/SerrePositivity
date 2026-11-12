module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectModels
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.InfinityCategory
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeClosure
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FullInclusionLift
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FullZeroObject

/-! # 導来 ∞ 圏の完全対象の充満部分

概要：有界有限射影複体と擬同型な semifree 複体の全頂点が張る Perf(S) を定義する。
方針：充満部分単体集合を正本とし、計算用の充満 dg 部分圏の nerve との同型を与える。
規約：有限生成射影を用い、自由性や局所環の仮定を課さない。
使われ方：K 理論の G2 の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
open scoped _root_.Simplicial ZeroObject
variable (S : Type u) [CommRing S]

/-- 概要：完全な semifree 複体の対象条件。
方針：semifree 複体に完全モデル条件を課す。
規約：既存の complexSemifree を変更しない。使われ方：Perf の対象。 -/
def perfectSemifreeProperty (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) : Prop := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPerfectModel S P.val

/-- 概要：完全な semifree 複体の充満 dg 部分圏。
方針：Hom 複体をそのまま制限する。
規約：semifree の全複体と同じ射。使われ方：Perf の計算モデル。 -/
abbrev PerfectSemifree := DGFullSubcategory (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (perfectSemifreeProperty S)

/-- 概要：Perf(S) の充満 dg nerve モデル。
方針：完全な semifree 複体の dg nerve を取る。
規約：正本の全部分単体集合とは下の標準同型で結ぶ。使われ方：演算とホモトピー圏の計算。 -/
def perfectNerveModel : SSet.{u + 1} := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (PerfectSemifree S)

/-- 概要：Perf の計算モデルから D(S) への包含。
方針：充満 dg 包含に dg nerve を適用する。
規約：全ての Hom 成分を保持する。使われ方：像の記述と D4 の制限。 -/
def perfectNerveInclusion : perfectNerveModel S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (perfectSemifreeProperty S))

/-- 概要：D(S) の完全頂点で張られる充満部分単体集合 Perf(S)。
方針：全頂点の semifree 複体に完全モデル条件を課す。
規約：D(S) の実際の Subcomplex。使われ方：完全導来 ∞ 圏の正本。 -/
def perfectInfinitySubcomplex : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullOnObjects S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (perfectSemifreeProperty S)

/-- 概要：完全導来 ∞ 圏 Perf(S)。
方針：指定した充満部分単体集合の台を取る。
規約：D(S) の部分型としての単体集合。使われ方：K 理論の入力。 -/
abbrev perfectInfinityCategory : SSet.{u + 1} := perfectInfinitySubcomplex S

/-- 概要：計算モデルの包含の像は正本の Perf(S) である。
方針：充満 dg 包含の像の一般公式を使う。
規約：各次元での部分集合の等式。使われ方：充満部分としての同定。 -/
lemma perfectNerveInclusion_range :
    SSet.Subcomplex.range (perfectNerveInclusion S) = perfectInfinitySubcomplex S :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.range_inclusion S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (perfectSemifreeProperty S)

/-- 概要：完全 dg nerve モデルの包含は単射射である。
方針：充満 dg 包含の nerve の単射性を使う。
規約：各次元で単射。使われ方：像との同型。 -/
instance perfectNerveInclusion_mono : Mono (perfectNerveInclusion S) := by
  dsimp [perfectNerveInclusion]
  infer_instance

/-- 概要：完全 dg nerve の計算モデルと正本の Perf(S) は単体的に同型である。
方針：単射な包含からその像への同型と像の等式を合成する。
規約：弱同値より強い実際の同型。使われ方：計算モデルから正本への転送。 -/
def perfectNerveModelIso : perfectNerveModel S ≅ perfectInfinityCategory S :=
  asIso (SSet.Subcomplex.toRange (perfectNerveInclusion S)) ≪≫
    eqToIso (congrArg (fun K : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S).Subcomplex => (K : SSet.{u + 1}))
      (perfectNerveInclusion_range S))

/-- 概要：完全 dg nerve の計算モデルは quasicategory である。
方針：N2 の一般の dg nerve の定理を具体化する。
規約：可換環以外の仮定なし。使われ方：Perf の内部ホーン充填。 -/
instance perfectNerveModel_quasicategory : SSet.Quasicategory (perfectNerveModel S) := by
  dsimp [perfectNerveModel]
  infer_instance

/-- 概要：正本の充満部分単体集合 Perf(S) は quasicategory である。
方針：計算モデルとの単体的同型で内部ホーンの充填を移す。
規約：元の D(S) の部分集合として主張する。使われ方：Perf のホモトピー圏。 -/
instance perfectInfinityCategory_quasicategory :
    SSet.Quasicategory (perfectInfinityCategory S) where
  hornFilling' {n} {i} b h0 hn := by
    obtain ⟨f, hf⟩ := SSet.Quasicategory.hornFilling h0 hn (b ≫ (perfectNerveModelIso S).inv)
    refine ⟨f ≫ (perfectNerveModelIso S).hom, ?_⟩
    rw [← Category.assoc, ← hf, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 概要：Perf の対象条件は有界有限射影複体への擬同型で判定できる。
方針：semifree 複体上の完全モデルの判定式を使う。
規約：擬同型の向きは semifree 代表から有限射影代表へ。使われ方：定義の具体的展開。 -/
theorem perfectSemifreeProperty_iff (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) :
    perfectSemifreeProperty S P ↔ ∃ K : _root_.SerrePositivity.DifferentialGraded.Complex S, strictlyPerfectComplex S K ∧
      ∃ q : P.val ⟶ K, QuasiIso q :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPerfectModel_iff_quasiIso S P.val P.property

/-- 概要：零複体は完全な semifree 複体である。
方針：それぞれの零複体の所属を組にする。
規約：既存の零複体。使われ方：Perf の零対象の代表。 -/
def perfectSemifreeZero : PerfectSemifree S :=
  ⟨⟨0, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_zero S⟩, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPerfectModel_zero S⟩

/-- 概要：完全な semifree 複体は整数シフトで閉じる。
方針：semifree 性と完全モデル条件のシフト閉性を組にする。
規約：D3 と同じ複体シフト。使われ方：Perf のシフト閉性。 -/
def perfectSemifreeShift (P : PerfectSemifree S) (n : ℤ) : PerfectSemifree S :=
  ⟨⟨P.val.val⟦n⟧, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_shift S P.val.property n⟩,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPerfectModel_shift S P.property n⟩

/-- 概要：完全な semifree 複体間の任意の射の cone は同じ部分圏に属す。
方針：両方の対象条件の写像錐閉性を組にする。
規約：任意の鎖写像。使われ方：Perf の cone 閉性。 -/
def perfectSemifreeCone (P Q : PerfectSemifree S) (f : P.val.val ⟶ Q.val.val) :
    PerfectSemifree S :=
  ⟨⟨CochainComplex.mappingCone f, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_mappingCone f P.val.property Q.val.property⟩,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPerfectModel_mappingCone S f P.property Q.property⟩

/-- 概要：完全な semifree 複体間の任意の射の fiber は同じ部分圏に属す。
方針：cone の −1 シフトを取る。
規約：N7 と D4 の標準 fiber。使われ方：Perf の fiber 閉性。 -/
def perfectSemifreeFiber (P Q : PerfectSemifree S) (f : P.val.val ⟶ Q.val.val) :
    PerfectSemifree S := perfectSemifreeShift S (perfectSemifreeCone S P Q f) (-1)

/-- 概要：完全な semifree 複体の有限直和は同じ部分圏に属す。
方針：有限直和の二つの閉性を組にする。
規約：小さい有限添字集合。使われ方：Perf の有限直和閉性。 -/
def perfectSemifreeFiniteBiproduct {I : Type v} [Finite I] [Small.{u} I]
    (P : I → PerfectSemifree S) : PerfectSemifree S :=
  ⟨⟨⨁ (fun i => (P i).val.val),
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_finiteBiproduct S _ (fun i => (P i).val.property)⟩,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPerfectModel_finiteBiproduct S _ (fun i => (P i).property)⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
