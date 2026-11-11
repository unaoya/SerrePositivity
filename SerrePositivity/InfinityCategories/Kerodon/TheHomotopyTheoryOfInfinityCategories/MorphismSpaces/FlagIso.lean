module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PinchedReindex

/-!
概要：coherent nerve の右 pinched 写像空間を旗の解像の右随伴と同定する。
方針：各次数の旗の写像との同値と自然性を、宇宙の持ち上げを明示してまとめる。
規約：比較射の同値性自体は、解像の射影の相対的な同値性を別に要する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、Theorem 4.6.7.5（Tag 01LE）、coherent Hom の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：右 pinched 写像空間は豊穣 Hom に解像の右随伴を適用した単体集合。
方針：次数ごとの旗の写像との同値を、次数の自然性で自然同型にする。
規約：Hom の宇宙 u から coherent nerve の宇宙 max(u,v) へ持ち上げる。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、補助解像による写像空間の表示。 -/
noncomputable def coherentPinchedFlagIso {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) ≅
      (SSet.uliftFunctor.{v, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj (SimplicialCategory.sHom X Y)) :=
  NatIso.ofComponents (fun d ↦
    { hom := ↾fun τ ↦ ULift.up (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPinchedFlagMap τ))
      inv := ↾fun φ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentFlagPinchedSimplex φ.down.down
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro τ
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentFlagPinchedSimplex_flagMap τ
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro φ
        apply ULift.ext
        apply ULift.ext
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedFlagMap_flag φ.down.down }) (by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro τ
    apply ULift.ext
    apply ULift.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPinchedFlagMap_reindex τ α.unop)

/-- 概要：解像の射影の随伴による転置が与える標準の比較射。
方針：解像から元の単体集合への射影を Hom の随伴対応で移す。
規約：任意の単体集合 X に対して定義する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、coherent Hom の比較射の抽象的な表示。 -/
noncomputable def coherentResolutionComparison (X : SSet.{u}) :
    X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionHomEquiv X X (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app X)

/-- 概要：解像の標準比較射は各単体を射影の後の Yoneda 射に写す。
方針：随伴の単体ごとの計算、射影の自然性、標準単体での回収則を組み合わせる。
規約：制限 Yoneda 関手の単体は射の宇宙持ち上げ。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、具体的な coherent Hom 比較射との照合。 -/
lemma coherentResolutionComparison_app {X : SSet.{u}} {n : ℕ} (σ : X _⦋n⦌) :
    (coherentResolutionComparison X).app (Opposite.op ⦋n⦌) σ =
      ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n ≫ SSet.yonedaEquiv.symm σ) := by
  unfold coherentResolutionComparison
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionHomEquiv_app]
  apply ULift.ext
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionStdIso.inv.app ⦋n⦌ ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app Δ[n] ≫ SSet.yonedaEquiv.symm σ := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.naturality (SSet.yonedaEquiv.symm σ)]
      rfl
    _ = _ := by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll_std]

/-- 概要：coherent Hom の比較射は解像の標準比較射に対応する。
方針：各単体で比較した pinched 単体の旗の写像を計算する。
規約：右随伴の Hom の表示に移した後で二つの比較射を等置する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、Theorem 4.6.7.5（Tag 01LE）、比較射の同値性の還元。 -/
lemma coherentHomComparison_flagIso {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y ≫ (coherentPinchedFlagIso X Y).hom =
      (SSet.uliftFunctor.{v, u}).map
        (coherentResolutionComparison (SimplicialCategory.sHom X Y)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  apply ULift.ext
  change ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPinchedFlagMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonPinchedSimplex σ.down)) =
    (coherentResolutionComparison (SimplicialCategory.sHom X Y)).app (Opposite.op ⦋n⦌) σ.down
  rw [coherentResolutionComparison_app, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPinchedFlagMap_comparison]

/-- 概要：解像の標準比較射は単体集合 X に自然。
方針：各単体の計算式で Yoneda 射の後合成を使う。
規約：恒等関手から解像の右随伴への自然変換。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、比較射を写像空間の自然な比較として扱う。 -/
noncomputable def coherentResolutionComparisonNat : 𝟭 SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint where
  app X := coherentResolutionComparison X
  naturality {X Y} f := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro σ
    change (coherentResolutionComparison Y).app (Opposite.op ⦋n⦌)
      (f.app (Opposite.op ⦋n⦌) σ) =
      ULift.up (((coherentResolutionComparison X).app (Opposite.op ⦋n⦌) σ).down ≫ f)
    rw [coherentResolutionComparison_app, coherentResolutionComparison_app]
    apply ULift.ext
    simp only [ULift.down_up, Category.assoc, SSet.yonedaEquiv_symm_comp]

/-- 概要：解像の標準比較射は単射。
方針：各次数で解像の射影の切断を前合成し、元の Yoneda 射を回収する。
規約：X の Kan 性は仮定しない。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、比較射の相対的な拡張を扱うための包含。 -/
instance coherentResolutionComparison_mono (X : SSet.{u}) :
    Mono (coherentResolutionComparison X) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro σ τ h
  rw [coherentResolutionComparison_app, coherentResolutionComparison_app] at h
  have hh := congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSection n ≫ f.down) h
  simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSection_projection, Category.id_comp] at hh
  exact (SSet.yonedaEquiv (X := X) (n := ⦋n⦌)).symm.injective hh

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
