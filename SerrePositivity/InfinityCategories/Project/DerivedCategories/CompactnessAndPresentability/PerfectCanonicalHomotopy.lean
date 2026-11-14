module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.PerfectHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.PerfectInclusion

/-! # h Perf の標準包含

概要：単体集合の標準包含が h D(S) への充満忠実関手を誘導する。
方針：計算モデルの充満 dg 包含と N3 の比較を照合する。
規約：対象の選択を介した比較と標準包含を自然同型で結ぶ。
使われ方：h Perf を h D(S) の実際の充満部分圏として使う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (S : Type u) [CommRing S]

/-- 概要：モデルの包含と N3 の H⁰ 比較は自然に両立する。
方針：辺の代表上で閉零射の像を評価する。
規約：充満包含は Hom 複体上恒等。使われ方：標準包含の比較。 -/
def perfectModelH0InclusionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion S) ⋙ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).functor ≅
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equivalence S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectSemifree S)).functor ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectH0Inclusion S :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    rintro X Y ⟨e⟩
    dsimp
    simp only [Category.comp_id, Category.id_comp]
    rfl)

/-- 概要：Perf の標準単体包含が誘導するホモトピー関手。
方針：辺の類へ包含を適用する。
規約：正本の包含を直接使う。使われ方：h D(S) の充満部分圏。 -/
def perfectCanonicalHomotopyInclusion : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityHomotopyCategory S ⥤
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory S := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityInclusion S)

/-- 概要：標準包含の H⁰ 比較像は完全 dg 部分圏の H⁰ 包含と自然に同型である。
方針：正本と計算モデルの包含の等式と N3 の比較を使う。
規約：任意の可換環。使われ方：充満忠実性の転送。 -/
def perfectCanonicalH0Iso :
    perfectCanonicalHomotopyInclusion S ⋙ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).functor ≅
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityH0Equivalence S).functor ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectH0Inclusion S := by
  have h : perfectCanonicalHomotopyInclusion S =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectModelHomotopyEquivalence S).functor ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion S) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveModelIso S).inv ⋙ _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveModelIso_inv_inclusion]
  exact eqToIso (congrArg (fun F => F ⋙ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).functor) h) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (perfectModelH0InclusionIso S) ≪≫
      (Functor.associator _ _ _).symm

/-- 概要：Perf の標準包含はホモトピー圏で充満である。
方針：H⁰ 比較後の充満性を同値で反映する。
規約：全ての射のホモトピー類を含む。使われ方：h Perf の充満性。 -/
instance perfectCanonicalHomotopyInclusion_full : (perfectCanonicalHomotopyInclusion S).Full :=
  Functor.Full.of_comp_faithful_iso (perfectCanonicalH0Iso S)

/-- 概要：Perf の標準包含はホモトピー圏で忠実である。
方針：H⁰ 比較後の忠実性を使う。
規約：同じホモトピー関係を反映する。使われ方：h Perf の忠実性。 -/
instance perfectCanonicalHomotopyInclusion_faithful :
    (perfectCanonicalHomotopyInclusion S).Faithful :=
  Functor.Faithful.of_comp_iso (perfectCanonicalH0Iso S)

/-- 概要：標準包含と H⁰ を介した包含比較は自然に同型である。
方針：H⁰ 同値の単位と比較同型を合成する。
規約：どちらも同じ充満部分圏を与える。使われ方：代表を使う計算との整合。 -/
def perfectHomotopyInclusionIso :
    perfectCanonicalHomotopyInclusion S ≅ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectHomotopyInclusion S :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (perfectCanonicalH0Iso S) _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
