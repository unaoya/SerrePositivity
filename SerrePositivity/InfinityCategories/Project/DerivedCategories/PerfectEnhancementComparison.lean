module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectImage
public import SerrePositivity.DifferentialGraded.Perfect.Compact.FiniteGeneration

/-! # Perf の既存 perfect dg 加群との比較

概要：h Perf(S) は既存の一対象 dg 圏上の perfect dg 加群の H⁰ と同値である。
方針：有界有限射影複体のホモトピー圏の同型閉包を共通の本質像として使う。
規約：U13 の一対象・全生成集合の場合。使われ方：既存の K 理論との接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S]

/-- 概要：有界有限射影複体の像の同型閉包の充満部分圏。
方針：既存のホモトピー圏上の性質の同型閉包を取る。
規約：既存の strict 条件を変更しない。使われ方：二つの enhancement の共通像。 -/
abbrev RepletePerfectHomotopy := (perfectHomotopyProperty S).isoClosure.FullSubcategory

/-- 概要：h Perf の比較をその完全な本質像へ制限する。
方針：各対象に完全モデル条件の証明を添える。
規約：射は複体ホモトピー圏の射。使われ方：同値の構成。 -/
def perfectToRepleteHomotopy : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityHomotopyCategory S ⥤ RepletePerfectHomotopy S :=
  (perfectHomotopyProperty S).isoClosure.lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectComplexHomotopyInclusion S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectComplexHomotopyInclusion_obj S)

/-- 概要：h Perf から共通像への比較は圏同値である。
方針：充満忠実性と有限射影代表の semifree 解像度による本質的全射性を使う。
規約：有界な semifree 代表の存在は要求しない。使われ方：既存 perfect 圏との比較。 -/
instance perfectToRepleteHomotopy_isEquivalence : (perfectToRepleteHomotopy S).IsEquivalence := by
  have : (perfectToRepleteHomotopy S).Full := by dsimp [perfectToRepleteHomotopy]; infer_instance
  have : (perfectToRepleteHomotopy S).Faithful := by
    dsimp [perfectToRepleteHomotopy]; infer_instance
  have : (perfectToRepleteHomotopy S).EssSurj := ⟨fun X => by
    obtain ⟨Y, ⟨e⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectComplexHomotopyInclusion_essImage_iff S X.obj).2 X.property
    exact ⟨Y, ⟨(perfectHomotopyProperty S).isoClosure.isoMk e⟩⟩⟩
  exact { }

/-- 概要：既存の有限射影ホモトピー圏を同型閉包へ含める。
方針：strict な対象条件を同型閉包へ送る。
規約：既存の PerfectHomotopy の対象は変更しない。使われ方：共通像を経由する比較。 -/
def strictPerfectToRepleteHomotopy : PerfectHomotopy S ⥤ RepletePerfectHomotopy S :=
  (perfectHomotopyProperty S).isoClosure.lift (SerrePositivity.perfectHomotopyInclusion S)
    (fun X => (perfectHomotopyProperty S).le_isoClosure _ X.property)

/-- 概要：既存の有限射影ホモトピー圏から同型閉包への包含も同値である。
方針：定義による充満忠実性と同型閉包の代表の存在を使う。
規約：同型閉包と strict 像を同じ対象型とはみなさない。使われ方：同値の逆関手。 -/
instance strictPerfectToRepleteHomotopy_isEquivalence :
    (strictPerfectToRepleteHomotopy S).IsEquivalence := by
  have : (strictPerfectToRepleteHomotopy S).Full := by
    dsimp [strictPerfectToRepleteHomotopy]; infer_instance
  have : (strictPerfectToRepleteHomotopy S).Faithful := by
    dsimp [strictPerfectToRepleteHomotopy]; infer_instance
  have : (strictPerfectToRepleteHomotopy S).EssSurj := ⟨fun X => by
    obtain ⟨Y, hY, ⟨e⟩⟩ := X.property
    exact ⟨⟨Y, hY⟩, ⟨(perfectHomotopyProperty S).isoClosure.isoMk e.symm⟩⟩⟩
  exact { }

/-- 概要：h Perf(S) と既存の有限射影ホモトピー圏は同値である。
方針：共通の同型閉包への二つの同値を合成する。
規約：有限射影代表を選ぶ逆関手。使われ方：既存の perfect 資産との接続。 -/
def perfectInfinityStrictHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityHomotopyCategory S ≌ PerfectHomotopy S :=
  (perfectToRepleteHomotopy S).asEquivalence.trans
    (strictPerfectToRepleteHomotopy S).asEquivalence.symm

/-- 概要：h Perf(S) は U13 の一対象 perfect dg 加群の H⁰ と同値である。
方針：有限射影ホモトピー圏との比較と U13 の二つの既存同値を合成する。
規約：係数 S、一対象 PUnit、生成集合 Set.univ。使われ方：K 理論側の enhancement 比較。 -/
def perfectInfinityU13Equivalence : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityHomotopyCategory S ≌
    DifferentialGraded.HomotopyCategory S (PerfectDGModuleOver S PUnit.{1} Set.univ) :=
  (perfectInfinityStrictHomotopyEquivalence S).trans
    ((ringPerfectHomotopyEquivalence S).trans
      (perfectDGModuleHomotopyEquivalence S PUnit.{1} Set.univ).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
