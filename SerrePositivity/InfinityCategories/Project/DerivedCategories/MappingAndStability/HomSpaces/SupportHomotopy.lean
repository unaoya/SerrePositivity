module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.FullSemifreeHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.SupportClosure
public import SerrePositivity.PerfectComplex.ClosedSupport.Functoriality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.SemifreeResolution

/-! # h Perf_Z の有限射影代表による像

概要：h Perf_Z の複体ホモトピー圏での本質像はZ に台を持つ有界有限射影複体の像に一致する。
方針：一方は対象の完全モデル条件、他方は有限射影代表の semifree 解像度を使う。
規約：像は同型閉包を含めて比較する。使われ方：K 理論と既存の perfect 圏の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S] (Z : TopologicalSpace.Closeds (PrimeSpectrum S))

/-- 概要：Perf_Z の正本のホモトピー圏。
方針：二次切断を使う。規約：実際の全部分単体集合。使われ方：台つき比較。 -/
abbrev perfectSupportHomotopyCategory :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullHomotopyCategory S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportProperty S Z)

/-- 概要：台つき完全モデルの H⁰ 比較。
方針：一般の対象条件の比較を使う。規約：閉零射の類。使われ方：台つき比較。 -/
abbrev perfectSupportH0Equivalence :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullH0Equivalence S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportProperty S Z)

/-- 概要：台つき完全モデルの H⁰ 包含。
方針：充満 dg 包含を使う。規約：元の Hom。使われ方：台つき比較。 -/
abbrev perfectSupportH0Inclusion :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullH0Inclusion S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportProperty S Z)

/-- 概要：h Perf_Z の通常の複体ホモトピー圏への比較。
方針：完全 dg 部分圏の H⁰ を semifree の H⁰ に含めて既存の比較を取る。
規約：導来圏の宇宙の選択を要しない。使われ方：有限射影代表との像の比較。 -/
def perfectSupportComplexHomotopyInclusion : perfectSupportHomotopyCategory S Z ⥤
    _root_.HomotopyCategory (ModuleCat.{u} S) (.up ℤ) :=
  (perfectSupportH0Equivalence S Z).functor ⋙ perfectSupportH0Inclusion S Z ⋙
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S

/-- 概要：複体ホモトピー圏への比較は充満である。
方針：同値と二つの充満包含を合成する。
規約：全ての鎖写像のホモトピー類を含む。使われ方：本質像としての h Perf_Z。 -/
instance perfectSupportComplexHomotopyInclusion_full :
    (perfectSupportComplexHomotopyInclusion S Z).Full := by
  dsimp [perfectSupportComplexHomotopyInclusion, perfectSupportH0Inclusion]
  infer_instance

/-- 概要：複体ホモトピー圏への比較は忠実である。
方針：同値と二つの忠実比較を合成する。
規約：ホモトピー類の等式を反映する。使われ方：充満部分圏としての同定。 -/
instance perfectSupportComplexHomotopyInclusion_faithful :
    (perfectSupportComplexHomotopyInclusion S Z).Faithful := by
  dsimp [perfectSupportComplexHomotopyInclusion, perfectSupportH0Inclusion]
  infer_instance

/-- 概要：h Perf_Z の像は有界有限射影複体と同型なホモトピー圏の対象である。
方針：H⁰ の対象に付された完全モデル条件を取り出す。
規約：同型閉包で記述する。使われ方：本質像の片方向。 -/
lemma perfectSupportComplexHomotopyInclusion_obj (X : perfectSupportHomotopyCategory S Z) :
    (perfectHomotopyProperty S).isoClosure ((perfectSupportComplexHomotopyInclusion S Z).obj X) ∧
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportHomotopyProperty S Z ((perfectSupportComplexHomotopyInclusion S Z).obj X) := by
  let P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectSupportedSemifree S Z := ForgetEnrichment.to (Complex S)
    ((perfectSupportH0Equivalence S Z).functor.obj X).as
  exact ⟨P.property.1, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportHomotopyProperty_quotient S Z _).2 P.property.2⟩

/-- 概要：h Perf_Z の本質像は有界有限射影複体のホモトピー圏での像の同型閉包に一致する。
方針：有限射影代表に semifree 解像度を取り、その擬同型をホモトピー同値にする。
規約：有界有限射影複体が semifree であるとは仮定しない。使われ方：h Perf_Z の像の主定理。 -/
theorem perfectSupportComplexHomotopyInclusion_essImage_iff
    (X : _root_.HomotopyCategory (ModuleCat.{u} S) (.up ℤ)) :
    (∃ Y : perfectSupportHomotopyCategory S Z,
      Nonempty ((perfectSupportComplexHomotopyInclusion S Z).obj Y ≅ X)) ↔
        (perfectHomotopyProperty S).isoClosure X ∧ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportHomotopyProperty S Z X := by
  constructor
  · rintro ⟨Y, ⟨e⟩⟩
    exact ⟨(perfectHomotopyProperty S).isoClosure.prop_of_iso e
      (perfectSupportComplexHomotopyInclusion_obj S Z Y).1,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportHomotopyProperty S Z).prop_of_iso e
      (perfectSupportComplexHomotopyInclusion_obj S Z Y).2⟩
  · rintro ⟨⟨W, hW, ⟨e⟩⟩, hX⟩
    obtain ⟨K, rfl⟩ := W.quotient_obj_surjective
    have hK := (perfectHomotopyProperty_quotient S K).mp hW
    obtain ⟨P, q, hP, _, hq⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.exists_complexSemifree_resolution S K
    have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_isKProjective S hP
    have := _root_.SerrePositivity.DifferentialGraded.strictlyPerfectComplex_isKProjective S K hK
    have : IsIso ((HomotopyCategory.quotient _ _).map q) :=
      (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences q).2
        ((CochainComplex.IsKProjective.quasiIso_iff q).1 hq)
    have hsK : HasHomologySupportOn Z K := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportHomotopyProperty_quotient S Z K).1
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportHomotopyProperty S Z).prop_of_iso e hX)
    have hsP : HasHomologySupportOn Z P := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportHomotopyProperty_quotient S Z P).1
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportHomotopyProperty S Z).prop_of_iso
        (asIso ((HomotopyCategory.quotient _ _).map q)).symm
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportHomotopyProperty_quotient S Z K).2 hsK))
    let P' : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectSupportedSemifree S Z := ⟨⟨P, hP⟩,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPerfectModel_iff_quasiIso S P hP).2 ⟨K, hK, q, hq⟩, hsP⟩
    let Y := (toHomotopy S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectSupportedSemifree S Z)).obj (ForgetEnrichment.of (Complex S) P')
    let G := perfectSupportH0Inclusion S Z ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S
    exact ⟨(perfectSupportH0Equivalence S Z).inverse.obj Y,
      ⟨G.mapIso ((perfectSupportH0Equivalence S Z).counitIso.app Y) ≪≫
        asIso ((HomotopyCategory.quotient _ _).map q) ≪≫ e.symm⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
