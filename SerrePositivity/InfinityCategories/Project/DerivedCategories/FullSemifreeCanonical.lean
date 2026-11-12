module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FullSemifreeHomotopy

/-! # 全部分圏の正本の包含と計算モデルの比較

概要：正本の 全部分圏の包含は dg nerve モデルの包含と標準同型の下で一致する。
方針：像への分解と部分複体の等式の移送を計算する。
規約：単体集合の射の等式で比較する。使われ方：正本への引き戻し判定の転送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (S : Type u) [CommRing S] (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S → Prop)

/-- 概要：正本の 対象条件 P の部分圏 から D(S) への包含。
方針：充満部分単体集合の標準包含を取る。
規約：部分型の値を返す。使われ方：D4 の比較射の入力。 -/
abbrev semifreeFullInclusion :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullSubcomplex S P : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullSubcomplex S P).ι

private lemma subcomplex_eq_ι {X : SSet.{u}} (K L : X.Subcomplex) (h : K = L) :
    eqToHom (congrArg (fun M : X.Subcomplex => (M : SSet.{u})) h) ≫ L.ι = K.ι := by
  cases h
  exact Category.id_comp _

/-- 概要：計算モデルから正本を経由する包含は元の dg nerve 包含である。
方針：像への分解と等しい部分複体の包含の式を使う。
規約：実際の射の等式。使われ方：正本とモデルの包含の整合。 -/
lemma semifreeFullNerveIso_hom_inclusion :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerveIso S P).hom ≫ semifreeFullInclusion S P =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerveInclusion S P := by
  change (SSet.Subcomplex.toRange (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerveInclusion S P) ≫
    eqToHom (congrArg (fun K : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S).Subcomplex => (K : SSet.{u + 1}))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerveInclusion_range S P))) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullSubcomplex S P).ι = _
  rw [Category.assoc, subcomplex_eq_ι _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerveInclusion_range S P),
    SSet.Subcomplex.toRange_ι]

/-- 概要：正本から計算モデルを経由する包含は標準包含である。
方針：同型の順方向を前合成して逆則を消去する。
規約：モデルを経由した図式は周囲で同じ図式。使われ方：D4 の比較射の正本。 -/
lemma semifreeFullNerveIso_inv_inclusion :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerveIso S P).inv ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerveInclusion S P =
      semifreeFullInclusion S P := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerveIso S P).hom).1
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, semifreeFullNerveIso_hom_inclusion]

/-- 概要：モデルの包含と N3 の H⁰ 比較は自然に両立する。
方針：辺の代表上で閉零射の像を評価する。
規約：充満包含は Hom 複体上恒等。使われ方：標準包含の比較。 -/
def semifreeFullModelH0InclusionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerveInclusion S P) ⋙
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).functor ≅
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equivalence S (DGFullSubcategory (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) P)).functor ⋙
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullH0Inclusion S P :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    rintro X Y ⟨e⟩
    dsimp
    simp only [Category.comp_id, Category.id_comp]
    rfl)

/-- 概要：全部分圏の標準単体包含が誘導するホモトピー関手。
方針：辺の類へ包含を適用する。
規約：正本の包含を直接使う。使われ方：h D(S) の充満部分圏。 -/
def semifreeFullCanonicalHomotopyInclusion : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullHomotopyCategory S P ⥤
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory S := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map (semifreeFullInclusion S P)

/-- 概要：標準包含の H⁰ 比較像は充満 dg 部分圏の H⁰ 包含と自然に同型である。
方針：正本と計算モデルの包含の等式と N3 の比較を使う。
規約：任意の可換環。使われ方：充満忠実性の転送。 -/
def semifreeFullCanonicalH0Iso :
    semifreeFullCanonicalHomotopyInclusion S P ⋙ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).functor ≅
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullH0Equivalence S P).functor ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullH0Inclusion S P := by
  have h : semifreeFullCanonicalHomotopyInclusion S P =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullModelHomotopyEquivalence S P).functor ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerveInclusion S P) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerveIso S P).inv ⋙ _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map_comp, semifreeFullNerveIso_inv_inclusion]
  exact eqToIso (congrArg (fun F => F ⋙ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).functor) h) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (semifreeFullModelH0InclusionIso S P) ≪≫
      (Functor.associator _ _ _).symm

/-- 概要：全部分圏の標準包含はホモトピー圏で充満である。
方針：H⁰ 比較後の充満性を同値で反映する。
規約：全ての射のホモトピー類を含む。使われ方：全部分圏のホモトピー圏 の充満性。 -/
instance semifreeFullCanonicalHomotopyInclusion_full : (semifreeFullCanonicalHomotopyInclusion S P).Full :=
  Functor.Full.of_comp_faithful_iso (semifreeFullCanonicalH0Iso S P)

/-- 概要：全部分圏の標準包含はホモトピー圏で忠実である。
方針：H⁰ 比較後の忠実性を使う。
規約：同じホモトピー関係を反映する。使われ方：全部分圏のホモトピー圏 の忠実性。 -/
instance semifreeFullCanonicalHomotopyInclusion_faithful :
    (semifreeFullCanonicalHomotopyInclusion S P).Faithful :=
  Functor.Faithful.of_comp_iso (semifreeFullCanonicalH0Iso S P)

/-- 概要：標準包含と H⁰ を介した包含比較は自然に同型である。
方針：H⁰ 同値の単位と比較同型を合成する。
規約：どちらも同じ充満部分圏を与える。使われ方：代表を使う計算との整合。 -/
def semifreeFullHomotopyInclusionIso :
    semifreeFullCanonicalHomotopyInclusion S P ≅ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullHomotopyInclusion S P :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (semifreeFullCanonicalH0Iso S P) _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
