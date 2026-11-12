module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftComparisonComponent
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaHomUniversal

/-!
概要：任意の指定された左 Kan 変換の大域的 Hom 普遍性。
方針：構成済みの普遍的候補からの比較射を各点で可逆と示し、指定変換を保って移す。
規約：普遍性を持つ別の変換の存在だけでは終えない。
使われ方：点ごとの左 Kan 条件から大域的一意性への接続。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：h Fun の指定二胞体は全ての頂点成分が可逆なら可逆。
方針：その二胞体のホモトピー代表に点ごとの辺の可逆性判定を適用する。
規約：始域に quasicategory 性は要求しない。
使われ方：局所 Kan 比較から大域的同型への移行。 -/
lemma kanFunctorHom_isIso_of_components {A D : SSet.{u}} [Quasicategory D]
    {F G : A ⟶ D} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) (hη : ∀ a : A _⦋0⦌, IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η a)) :
    IsIso η := by
  have hv : ∀ a : A _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy η) a).toTruncated := by
    intro a
    change IsIso (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy η) a).toTruncated)
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_component]
    exact hη a
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy η) hv
  change IsIso (SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy η))) at h
  rwa [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom] at h

/-- 概要：指定変換を保つ左 Kan 拡張間の比較射は h Fun で可逆。
方針：局所普遍余錐による比較射の各点での可逆性を大域的判定へ渡す。
規約：同型の存在から指定比較射の可逆性を推論しない。
使われ方：候補の普遍性を既存の指定変換へ移す。 -/
lemma kanLeftComparison_isIso {K C D : SSet.{u}} [Quasicategory D] (δ : K ⟶ C)
    {F₀ : K ⟶ D} {F G : C ⟶ D}
    (β : SSet.Homotopy F₀ (δ ≫ F)) (γ : SSet.Homotopy F₀ (δ ≫ G))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ F β) (hγ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ G γ)
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G)
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap δ (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)) G η =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy γ)) : IsIso η :=
  kanFunctorHom_isIso_of_components η
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftComparison_component_isIso δ β γ hβ hγ η hη)

/-- 概要：左 Kan の Hom 普遍性は指定変換に両立する標的同型で移送できる。
方針：標的同型による Hom 全単射を元の Kan 比較写像と合成する。
規約：移送先の指定変換 γ との両立を明示する。
使われ方：点ごとに普遍な任意の指定変換への普遍性の移送。 -/
lemma kanLeftHomUniversal_of_iso {K C D : SSet.{u}} (δ : K ⟶ C)
    {F₀ : K ⟶ D} {F G : C ⟶ D} (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ F)) (γ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ G))
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) (hi : IsIso η) (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap δ β G η = γ)
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal δ β) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal δ γ := by
  have : IsIso η := hi
  intro Z
  have he : Function.Bijective (fun θ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom G Z ↦ η ≫ θ) := by
    have h := (Iso.homCongr (asIso η).symm
      (Iso.refl (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex Z)))).bijective
    change Function.Bijective (fun θ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom G Z ↦ η ≫ θ ≫ 𝟙 _) at h
    simpa only [Category.comp_id] using h
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap δ γ Z = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap δ β Z) ∘ (fun θ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom G Z ↦ η ≫ θ) := by
    funext θ
    rw [← hη]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap, Function.comp_apply, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hf]
  exact (hβ Z).comp he

/-- 概要：任意の指定された左 Kan 変換は h Fun の大域的 Hom 普遍性を持つ。
方針：局所余極限から普遍的候補を構成し、指定変換へ比較して可逆性で普遍性を移す。
規約：元の β の類そのものの比較写像の全単射性を結論する。
使われ方：Kerodon Proposition 7.3.6.1（Tag 0309） の Hom 普遍性と大域的一意性。 -/
lemma kanLeftKanExtension_homUniversal {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] (δ : K ⟶ C)
    {F₀ : K ⟶ D} {F : C ⟶ D} (β : SSet.Homotopy F₀ (δ ≫ F))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ F β) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal δ
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)) := by
  have hlocal : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c) := by
    intro c
    obtain ⟨t, ht, _⟩ := hβ.colimitValue c
    exact ⟨t, ht⟩
  obtain ⟨L, α, hα, hu⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_with_homUniversal_of_local_colimits δ F₀ hlocal
  obtain ⟨η, hη⟩ := (hu F).2
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β))
  exact kanLeftHomUniversal_of_iso δ _ _ η (kanLeftComparison_isIso δ α β hα hβ η hη) hη hu

/-- 概要：h Fun の指定射に対する左 Kan 条件から、その射の Hom 普遍性を得る。
方針：指定射のホモトピー代表へ適用し、代表の類の回収で戻す。
規約：代表の選択は結論に残さない。
使われ方：自然変換を h Fun の射として与える利用側の界面。 -/
lemma kanLeftKanExtensionHom_homUniversal {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] (δ : K ⟶ C)
    (F₀ : K ⟶ D) (F : C ⟶ D) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ F))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtensionHom δ F₀ F β) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal δ β := by
  have h := kanLeftKanExtension_homUniversal δ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy β) hβ
  rwa [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom] at h

/-- 概要：二つの左 Kan 拡張の図式を指定変換に両立する大域的同型で比較する。
方針：点ごとの Kan 条件から導いた両方の Hom 普遍性で比較同型を構成する。
規約：hD の各点の同型の族ではなく h Fun(C,D) の同型を返す。
使われ方：左 Kan 拡張の大域的一意性。 -/
def kanLeftKanExtensionIso {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] (δ : K ⟶ C)
    {F₀ : K ⟶ D} {F G : C ⟶ D}
    (β : SSet.Homotopy F₀ (δ ≫ F)) (γ : SSet.Homotopy F₀ (δ ≫ G))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ F β) (hγ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ G γ) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomUniversalIso δ _ _ (kanLeftKanExtension_homUniversal δ β hβ)
    (kanLeftKanExtension_homUniversal δ γ hγ)

/-- 概要：構成した左 Kan 比較同型は元の二つの指定変換に両立する。
方針：Hom 普遍性から構成した比較同型の仕様を使う。
規約：式に現れる β と γ は元の指定変換の類。
使われ方：変換を保持した大域的同型の回収。 -/
lemma kanLeftKanExtensionIso_hom_fac {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] (δ : K ⟶ C)
    {F₀ : K ⟶ D} {F G : C ⟶ D}
    (β : SSet.Homotopy F₀ (δ ≫ F)) (γ : SSet.Homotopy F₀ (δ ≫ G))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ F β) (hγ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ G γ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap δ (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)) G
        (kanLeftKanExtensionIso δ β γ hβ hγ).hom =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy γ) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomUniversalIso_hom_fac δ _ _ (kanLeftKanExtension_homUniversal δ β hβ)
    (kanLeftKanExtension_homUniversal δ γ hγ)

/-- 概要：指定変換に両立する左 Kan 比較射は構成した比較同型の順方向の射に一意。
方針：元の左 Kan 変換による Hom 比較写像の単射性を使う。
規約：射の型は h Fun(C,D) の Hom。
使われ方：変換を保つ左 Kan 拡張の大域的一意性。 -/
lemma kanLeftKanExtensionIso_hom_unique {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] (δ : K ⟶ C)
    {F₀ : K ⟶ D} {F G : C ⟶ D}
    (β : SSet.Homotopy F₀ (δ ≫ F)) (γ : SSet.Homotopy F₀ (δ ≫ G))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ F β) (hγ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ G γ)
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G)
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap δ (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)) G η =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy γ)) :
    η = (kanLeftKanExtensionIso δ β γ hβ hγ).hom :=
  (kanLeftKanExtension_homUniversal δ β hβ G).1
    (hη.trans (kanLeftKanExtensionIso_hom_fac δ β γ hβ hγ).symm)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
