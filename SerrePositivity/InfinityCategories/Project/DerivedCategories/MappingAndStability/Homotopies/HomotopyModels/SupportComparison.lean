module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.SupportHomotopy

/-! # 台つき完全導来 ∞ 圏と既存の台つきホモトピー圏

概要：h Perf_Z(S) は既存の幾何学的台つき perfect 圏と同値である。
方針：複体ホモトピー圏での共通の本質像を経由する。
規約：任意の閉集合、任意の可換環。使われ方：scalarSupported と K₀ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S] (Z : TopologicalSpace.Closeds (PrimeSpectrum S))

/-- 概要：台つき完全対象のホモトピー圏での共通像。
方針：完全性の同型閉包と幾何学的台を同時に課す。
規約：元の複体ホモトピー圏の全部分圏。使われ方：二つの表示の比較。 -/
def repletePerfectSupportProperty :
    ObjectProperty (_root_.HomotopyCategory (ModuleCat.{u} S) (.up ℤ)) :=
  (perfectHomotopyProperty S).isoClosure ⊓ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportHomotopyProperty S Z

/-- 概要：共通像は同型で閉じる。
方針：二つの条件の同型不変性を使う。
規約：完全性と台の交わり。使われ方：代表の変更。 -/
instance repletePerfectSupportProperty_isoClosed :
    (repletePerfectSupportProperty S Z).IsClosedUnderIsomorphisms := by
  dsimp [repletePerfectSupportProperty]
  infer_instance

/-- 概要：h Perf_Z の比較を本質像に制限する。
方針：像の二つの対象条件を付ける。
規約：射は同じホモトピー類。使われ方：圏同値の構成。 -/
def perfectSupportToReplete : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportHomotopyCategory S Z ⥤
    (repletePerfectSupportProperty S Z).FullSubcategory :=
  (repletePerfectSupportProperty S Z).lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportComplexHomotopyInclusion S Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportComplexHomotopyInclusion_obj S Z)

/-- 概要：h Perf_Z から共通像への比較は圏同値である。
方針：充満忠実性と semifree 解像度による本質的全射性。
規約：有界 semifree 代表を要求しない。使われ方：台つき比較。 -/
instance perfectSupportToReplete_isEquivalence :
    (perfectSupportToReplete S Z).IsEquivalence := by
  have : (perfectSupportToReplete S Z).Full := by dsimp [perfectSupportToReplete]; infer_instance
  have : (perfectSupportToReplete S Z).Faithful := by
    dsimp [perfectSupportToReplete]; infer_instance
  have : (perfectSupportToReplete S Z).EssSurj := ⟨fun X => by
    obtain ⟨Y, ⟨e⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportComplexHomotopyInclusion_essImage_iff S Z X.obj).2 X.property
    exact ⟨Y, ⟨(repletePerfectSupportProperty S Z).isoMk e⟩⟩⟩
  exact { }

/-- 概要：既存の幾何学的台つき perfect 圏を共通像へ含める。
方針：strict 条件をその同型閉包へ送る。
規約：既存の圏の対象を変更しない。使われ方：比較同値の逆向き。 -/
def strictPerfectSupportToReplete : SupportedPerfectHomotopyOn Z ⥤
    (repletePerfectSupportProperty S Z).FullSubcategory :=
  (repletePerfectSupportProperty S Z).lift
    (supportedPerfectOnInclusion Z ⋙ SerrePositivity.perfectHomotopyInclusion S)
    (fun X => ⟨(perfectHomotopyProperty S).le_isoClosure _ X.obj.property, X.property⟩)

/-- 概要：既存の台つき perfect 圏から共通像への包含は同値である。
方針：同型閉包の有限射影代表へ台条件を移す。
規約：任意の閉集合。使われ方：台つき圏の同定。 -/
instance strictPerfectSupportToReplete_isEquivalence :
    (strictPerfectSupportToReplete S Z).IsEquivalence := by
  have : (strictPerfectSupportToReplete S Z).Full := by
    dsimp [strictPerfectSupportToReplete]; infer_instance
  have : (strictPerfectSupportToReplete S Z).Faithful := by
    dsimp [strictPerfectSupportToReplete]; infer_instance
  have : (strictPerfectSupportToReplete S Z).EssSurj := ⟨fun X => by
    obtain ⟨Y, hY, ⟨e⟩⟩ := X.property.1
    have hs : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportHomotopyProperty S Z Y :=
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportHomotopyProperty S Z).prop_of_iso e X.property.2
    exact ⟨⟨⟨Y, hY⟩, hs⟩, ⟨(repletePerfectSupportProperty S Z).isoMk e.symm⟩⟩⟩
  exact { }

/-- 概要：h Perf_Z は既存の幾何学的台つき perfect ホモトピー圏と同値である。
方針：共通像への二つの同値を合成する。
規約：任意の可換環と閉集合。使われ方：既存 K₀WithSupport との比較。 -/
def perfectSupportClosedEquivalence : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportHomotopyCategory S Z ≌
    SupportedPerfectHomotopyOn Z :=
  (perfectSupportToReplete S Z).asEquivalence.trans
    (strictPerfectSupportToReplete S Z).asEquivalence.symm

/-- 概要：有限生成イデアルの台では h Perf_Z は scalarSupported 版とも同値である。
方針：完全対象上の既存の幾何学的台・スカラー台同値を合成する。
規約：一般の D_Z にはこの同値を主張しない。使われ方：既存の台つき K 理論。 -/
def perfectSupportScalarEquivalence {e : ℕ} (z : Fin e → S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportHomotopyCategory S (supportZeroLocus (Ideal.span (Set.range z))) ≌
      SupportedPerfectHomotopy z :=
  (perfectSupportClosedEquivalence S _).trans (supportedPerfectClosedEquivalence z).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
